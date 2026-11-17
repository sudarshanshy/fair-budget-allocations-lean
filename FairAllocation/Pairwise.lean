import FairAllocation.Fractional
import FairAllocation.Order

set_option autoImplicit false

/-!
# The appendix's pairwise EF2 argument

The proof uses the first prefix where EF1 fails, rather than explicitly
minimizing `EFCount`. This gives the same two deletion witnesses as Lemmas
8--10 and 12. `critical_prefix_bounds` is Claim 13; the density comparison
inside `critical_remainder` is Claim 14, and its conclusion is Lemma 15.

The two hypotheses `Priority` and `TerminalPriority` are properties of the
actual greedy run, proved in `Invariants.lean`, not assumptions on the input.
-/

namespace FairAllocation

variable {G : Type*}

/-- Proposition 4, stated with weak density comparison to allow ties. -/
def Priority (v s : G → ℚ) (B : ℚ) (X Y : List G) : Prop :=
  ∀ P x Q y, Before X P x → Before Y Q y →
    total v P < total v Q → total s P + s y ≤ B → v y / s y ≤ v x / s x

/-- The terminal case of Proposition 4: if `X` has no next good, a
strictly-envied prefix's next good cannot fit. -/
def TerminalPriority (v s : G → ℚ) (B : ℚ) (X Y : List G) : Prop :=
  ∀ Q y, Before Y Q y → total v X < total v Q → B < total s X + s y

theorem Priority.sublist_right {v s : G → ℚ} (hv : ∀ g, 0 ≤ v g)
    {B : ℚ} {X Y Z : List G} (h : Priority v s B X Y) (hZY : Z.Sublist Y) :
    Priority v s B X Z := by
  intro P x Q y hX hZ hval hfit
  obtain ⟨R, hR, hQR⟩ := hZ.of_sublist hZY
  exact h P x R y hX hR (hval.trans_le (total_sublist hv hQR)) hfit

theorem TerminalPriority.sublist_right {v s : G → ℚ} (hv : ∀ g, 0 ≤ v g)
    {B : ℚ} {X Y Z : List G} (h : TerminalPriority v s B X Y) (hZY : Z.Sublist Y) :
    TerminalPriority v s B X Z := by
  intro Q y hZ hval
  obtain ⟨R, hR, hQR⟩ := hZ.of_sublist hZY
  exact h R y hR (hval.trans_le (total_sublist hv hQR))

/-- The first transition from EF1 to failure of EF1. This is the discrete
intermediate-value argument of Lemmas 8--9, with explicit witnesses. -/
theorem exists_critical_prefix {v s : G → ℚ} (hs : ∀ g, 0 < s g)
    {X Z : List G} (hbad : ¬ EF 1 v (prefixValue v s X (total s Z)) Z) :
    ∃ P g Q, Z = P ++ g :: Q ∧
      EF 1 v (prefixValue v s X (total s P)) P ∧
      ¬ EF 1 v (prefixValue v s X (total s P + s g)) (P ++ [g]) := by
  induction Z using List.reverseRecOn with
  | nil =>
    apply hbad.elim
    simp [prefixValue_zero hs]
  | append_singleton Z g ih =>
    by_cases hprev : EF 1 v (prefixValue v s X (total s Z)) Z
    · exact ⟨Z, g, [], rfl, hprev, by simpa using hbad⟩
    · obtain ⟨P, x, Q, hZ, hP, hfail⟩ := ih hprev
      exact ⟨P, x, Q ++ [g], by simp [hZ], hP, hfail⟩

/-- Claim 13: the high-density part of `X` is small and has less value than
the prefix immediately before the critical good. -/
theorem critical_prefix_bounds {v s : G → ℚ}
    (hv : ∀ g, 0 ≤ v g) (hs : ∀ g, 0 < s g)
    {X D R P : List G} {g : G}
    (hX : X = D ++ R) (hdense : ∀ x ∈ D, v g / s g ≤ v x / s x)
    (hprev : EF 1 v (prefixValue v s X (total s P)) P)
    (hbad : ¬ EF 1 v (prefixValue v s X (total s P + s g)) (P ++ [g])) :
    total s D ≤ total s P + s g ∧ total v D < total v P := by
  have hP0 : 0 ≤ total s P := total_nonneg (fun x _ => (hs x).le)
  have hsize : total s D ≤ total s P + s g := by
    by_contra h
    have hcap : total s P + s g ≤ total s D := le_of_lt (lt_of_not_ge h)
    have hinc := prefixValue_increment hs
      (fun x hx => (le_density_iff hs).mp (hdense x hx)) hP0
      (show total s P ≤ total s P + s g by linarith [hs g]) hcap
    have hlow : total s P ≤ total s D := by linarith [hs g]
    have h₀ : prefixValue v s X (total s P) = prefixValue v s D (total s P) := by
      rw [hX, prefixValue_append_of_le hs D R hlow]
    have h₁ : prefixValue v s X (total s P + s g) =
        prefixValue v s D (total s P + s g) := by
      rw [hX, prefixValue_append_of_le hs D R hcap]
    have hmul := density_mul_size (v := v) hs g
    apply hbad
    apply (hprev.append_good g).mono_value
    rw [h₀, h₁]
    nlinarith
  refine ⟨hsize, ?_⟩
  have hval : total v D ≤ prefixValue v s X (total s P + s g) := by
    rw [hX, prefixValue_append, prefixValue_full hs D hsize]
    exact le_add_of_nonneg_right (prefixValue_nonneg hs (fun x _ => hv x) _)
  by_contra h
  have hle : total v P ≤ prefixValue v s X (total s P + s g) :=
    (le_of_not_gt h).trans hval
  exact hbad ((ef_of_total_le (k := 0) hle).discard_good g)

/-- Lemma 15, including the terminal case where the dense part is all of X. -/
theorem critical_remainder {v s : G → ℚ}
    (hv : ∀ g, 0 ≤ v g) (hs : ∀ g, 0 < s g)
    {B : ℚ} {X P Q : List G} {g : G}
    (horder : DensitySorted v s X)
    (hpriority : Priority v s B X (P ++ g :: Q))
    (hterminal : TerminalPriority v s B X (P ++ g :: Q))
    (hfeas : total s (P ++ g :: Q) ≤ B)
    (hprev : EF 1 v (prefixValue v s X (total s P)) P)
    (hbad : ¬ EF 1 v (prefixValue v s X (total s P + s g)) (P ++ [g])) :
    total v Q ≤ total v X - prefixValue v s X (total s P) := by
  obtain ⟨D, R, hX, hdense, hlow⟩ := density_split horder (v g / s g)
  obtain ⟨hsize, hval⟩ := critical_prefix_bounds hv hs hX hdense hprev hbad
  have hblocked : B < total s D + s g := by
    by_contra hn
    have hfit : total s D + s g ≤ B := le_of_not_gt hn
    cases R with
    | nil =>
      have ht := hterminal P g ⟨Q, rfl⟩ (by simpa [hX] using hval)
      exact (not_lt_of_ge hfit) (by simpa [hX] using ht)
    | cons x R =>
      have hge := hpriority D x P g ⟨R, hX⟩ ⟨Q, rfl⟩ hval hfit
      exact (not_le_of_gt (hlow x (by simp))) hge
  have hQ0 : 0 ≤ total s Q := total_nonneg (fun x _ => (hs x).le)
  have hP0 : 0 ≤ total s P := total_nonneg (fun x _ => (hs x).le)
  have hcap : total s P ≤ total s D := by
    simp only [total_append, total_cons] at hfeas
    linarith
  have hremaining : total s Q ≤ total s D - total s P := by
    simp only [total_append, total_cons] at hfeas
    linarith
  have hsub : total v D ≤ total v X := by
    rw [hX, total_append]
    exact le_add_of_nonneg_right (total_nonneg (fun x _ => hv x))
  have hpref : prefixValue v s X (total s P) = prefixValue v s D (total s P) := by
    rw [hX, prefixValue_append_of_le hs D R hcap]
  by_cases hQ : Q = []
  · subst Q
    simp only [total_nil]
    exact sub_nonneg.mpr (prefixValue_le_total hs (fun x _ => hv x) _)
  obtain ⟨q, hq, hmax⟩ := exists_max_weight (fun x => v x / s x) hQ
  have hd0 : 0 ≤ v q / s q := div_nonneg (hv q) (hs q).le
  have hcross : ∀ x ∈ D, v q / s q ≤ v x / s x := by
    intro x hx
    obtain ⟨Dx, Rx, hDx, _⟩ := List.eq_append_cons_of_mem hx
    obtain ⟨Qq, Rq, hQq, _⟩ := List.eq_append_cons_of_mem hq
    have hxBefore : Before X Dx x := by
      refine ⟨Rx ++ R, ?_⟩
      simp [hX, hDx, List.append_assoc]
    have hqBefore : Before (P ++ g :: Q) (P ++ g :: Qq) q := by
      exact ⟨Rq, by simp [hQq, List.append_assoc]⟩
    have hDxV : total v Dx ≤ total v D :=
      total_sublist hv (by rw [hDx]; exact List.sublist_append_left _ _)
    have hDxS : total s Dx ≤ total s D :=
      total_sublist (fun x => (hs x).le) (by rw [hDx]; exact List.sublist_append_left _ _)
    have hPV : total v P ≤ total v (P ++ g :: Qq) :=
      total_sublist hv (List.sublist_append_left _ _)
    have hqS : s q ≤ total s Q := total_le_of_mem (fun x => (hs x).le) hq
    apply hpriority Dx x (P ++ g :: Qq) q hxBefore hqBefore
      (hDxV.trans_lt (hval.trans_le hPV))
    simp only [total_append, total_cons] at hfeas
    linarith
  have hinc := prefixValue_increment hs
    (fun x hx => (le_density_iff hs).mp (hcross x hx)) hP0 hcap (le_refl (total s D))
  rw [prefixValue_full hs D le_rfl] at hinc
  have htail : total v Q ≤ (v q / s q) * total s Q := by
    calc
      total v Q ≤ total (fun x => (v q / s q) * s x) Q :=
        total_mono (fun x hx => (density_le_iff hs).mp (hmax x hx))
      _ = _ := total_mul _ _ _
  have hmul := mul_le_mul_of_nonneg_left hremaining hd0
  rw [hpref]
  linarith

/-- The central mathematical implication behind Theorem 5. -/
theorem pairwise_ef2 {v s : G → ℚ}
    (hv : ∀ g, 0 ≤ v g) (hs : ∀ g, 0 < s g)
    {B : ℚ} {X Z : List G}
    (horder : DensitySorted v s X)
    (hpriority : Priority v s B X Z)
    (hterminal : TerminalPriority v s B X Z)
    (hfeas : total s Z ≤ B) : EF 2 v (total v X) Z := by
  by_cases h : EF 1 v (prefixValue v s X (total s Z)) Z
  · exact (h.mono_value (prefixValue_le_total hs (fun g _ => hv g) _)).mono_count (by omega)
  obtain ⟨P, g, Q, rfl, hprev, hbad⟩ := exists_critical_prefix hs h
  have htail := critical_remainder hv hs horder hpriority hterminal hfeas hprev hbad
  have htwo := (hprev.discard_good g).append
    (ef_of_total_le (k := 0) (le_refl (total v Q)))
  have hresult := htwo.mono_value (show prefixValue v s X (total s P) + total v Q ≤
    total v X by linarith)
  simpa [List.append_assoc] using hresult

end FairAllocation

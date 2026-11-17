# Finding Fair Allocations under Budget Constraints — Lean formalization

This project formalizes **Appendix C, Theorem 5** of Barman, Khan, Shyam and Sreenivas, *Finding Fair Allocations under Budget Constraints* (AAAI 2023): density greedy achieves EF2 with **agent-specific sizes**. It also proves the stronger **EF1 guarantee against charity** (Lemma 11).

Source: [arXiv:2208.08168v2](https://arxiv.org/abs/2208.08168v2), [published article](https://doi.org/10.1609/aaai.v37i5.25681).

## Main results

`FairAllocation/Main.lean` exports:

- `densestGreedy_correct`: the executable algorithm returns a valid partition, respects every budget, is EF2 between agents and against charity, and is EF1 against charity.
- `densestGreedy_correct_finset`: the same fairness guarantees in finite-set notation, quantifying over **every feasible subset** of the compared bundle.
- `exists_feasible_ef2`: universal existence, witnessed by the algorithm itself.
- `commonSize_exists_ef2`: the main text's common-size existence result as a specialization.

`FairAllocation/Runtime.lean` proves at most `m + n` iterations and at most `2 * (m + n)^2` rational order comparisons. The cost counts the minimum-agent scan, feasibility filter, and maximum-density scan. A rational bit-complexity model is outside this formalization.

No result assumes the existence of a fair allocation or assumes that the algorithm satisfies a fairness certificate. The properties used by the mathematical proof are established by induction over the actual executable loop.

## Assumptions and definitions

There are `n` agents and `m` goods, represented by `Fin n` and `Fin m`. Values are identical across agents. Values and agent-specific sizes are **positive rational numbers**, as in the paper; budgets are nonnegative rationals, allowing zero budgets as well.

The algorithm chooses a least-valued active agent, then the densest remaining good that fits according to that agent's sizes. If no good fits, that agent becomes inactive. Input-list order breaks ties. The proof allows equal densities, without a perturbation assumption.

Bundles are lists in allocation order. `State.Valid` says that every good occurs exactly once across all agents and charity. It implies that bundles have no duplicates, different agents' bundles are disjoint, and charity is precisely the unallocated complement.

`EF k v u Z` means that deleting at most `k` entries of `Z` leaves value at most `u`. In particular, EF2 permits deleting two goods **together**. `SetEF` expresses the same guarantee using a deletion set of cardinality at most `k`. `FiniteSets.lean` proves the bridge from ordered sublists to arbitrary finite subsets. `PaperStatements.lean` additionally gives exactly two distinct deletion witnesses when the comparison set has at least two goods, and one actual deletion witness for each nonempty feasible charity subset, matching the paper's cardinality convention.

## Proof map

| Paper component | Formal component |
|---|---|
| Algorithm 2 | `Algorithm.lean`: `Instance.choose`, `Instance.run`, `densestGreedy` |
| Allocation validity and budget feasibility | `Partition.lean`, `Invariants.lean` |
| Allocation-order fractional prefixes, Definition 3 | `Fractional.lean`: `prefixValue` and its arithmetic properties |
| Proposition 4 and its terminal boundary case | `Invariants.lean`: `Invariant.priority`, `Invariant.terminalPriority` |
| Proposition 5 | `Invariants.lean`: `Invariant.poolPriority` |
| Lemma 11: EF1 against charity | `Charity.lean`: `charity_ef1` |
| Lemmas 8–10 and 12: crossing and deletion witnesses | `Pairwise.lean`: `exists_critical_prefix`; `Basic.lean`: `EF.append`, `EF.discard_good` |
| Claim 13 | `Pairwise.lean`: `critical_prefix_bounds` |
| Claim 14 and Lemma 15 | `Pairwise.lean`: `critical_remainder` |
| Theorem 5 | `Main.lean`: `densestGreedy_correct`, `densestGreedy_correct_finset` |
| Loop and comparison bounds | `Runtime.lean` |

The proof follows the appendix's allocation order for compared bundles; it does not assume that another agent's bundle is density-sorted from the observer's perspective. Instead of defining the minimum deletion count `EFCount`, it constructs deletion witnesses directly at the first prefix where EF1 fails. The dense-prefix argument also explicitly covers the case where the observer has no next good.

The main text's separate EF1 results for proportional, equal-size, and equal-value instances are outside this appendix-focused project. The common-size EF2 result is included as a corollary, and the paper's three-good tightness example is checked at ε = 1/10.

## Build and audit

The project pins Lean **4.33.1**, Mathlib **v4.33.1**, and dependency commits in `lake-manifest.json`.

From this directory, with Elan installed:

```sh
lake exe cache get
lake build
lake env lean FairAllocation/Audit.lean
```

`Audit.lean` prints the axioms of the exported correctness, existence, runtime, and counterexample theorems. Proofs contain no `sorry`, `admit`, custom axioms, or native-decision shortcuts. The only foundational axioms used are Lean/Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound` (individual theorems may use fewer).

`Examples.lean` contains kernel-checked computations for the paper's non-EF1 example, an instance with different agent-specific size rankings, and a zero-budget instance whose good stays in charity. These examples supplement the universal proofs.

For a focused check after dependencies are available, `scripts/check.py` checks named modules in the supplied dependency order and writes their compiled artifacts under `.lake/build/lib/lean`.

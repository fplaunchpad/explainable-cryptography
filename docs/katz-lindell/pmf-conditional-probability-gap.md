# Missing bridge: `PMF` ↔ `ProbabilityTheory.cond`

**Status:** observation / potential upstream Mathlib contribution, not yet investigated in depth.

## The gap

Mathlib has a mature, general-purpose conditional probability API for its
heavyweight `MeasureTheory.Measure` type:

- `Mathlib/Probability/ConditionalProbability.lean`
- `ProbabilityTheory.cond : Measure Ω → Set Ω → Measure Ω`, with notation
  `μ[|s]` (the measure conditioned on `s`) and `μ[t | s]` (the probability of
  `t` given `s`).
- Bayes' theorem is already proved: `cond_eq_inv_mul_cond_mul`.

Separately, Mathlib has `PMF` (`Mathlib.Probability.ProbabilityMassFunction`),
a lightweight type for *discrete* distributions — essentially a function to
`ℝ≥0∞` summing to 1 — with its own ergonomic `simp` set (`PMF.bind_apply`,
`PMF.pure_apply`, `PMF.tsum_coe`, ...) that makes reasoning about `do`-notation
probabilistic programs (exactly the style used throughout this project)
pleasant and automatable.

**What appears to be missing** is convenient glue between the two. `PMF.toMeasure`
does let you turn a `PMF` into a `Measure`, so `ProbabilityTheory.cond` is
technically *reachable* from a `PMF` — but once you cross into the general
`Measure` world you lose every `PMF`-specific simp lemma, and (as far as a
quick search of this checkout of Mathlib turned up) nobody has written the
connecting lemmas that would let you compute, e.g.,

```
(PMF.toMeasure p)[| {x | q x}] {y | r y}
```

back down into a concrete `tsum`/`ENNReal` arithmetic expression the way
`PMF.bind_apply` does for the unconditioned case. Without that bridge, doing
conditional-probability reasoning on a `PMF`-based proof means either:

1. dropping into the general `Measure` API and redoing a lot of the
   bookkeeping that `PMF`'s simp set normally handles for free, or
2. avoiding conditional-probability notation altogether and working with the
   equivalent unconditioned `tsum` arithmetic by hand (which is what
   `KatzLindell/PerfectSecrecy.lean` does throughout this repo).

## Why this came up here

While writing up `PerfectSecrecy.lean`'s `privKeav_eq` / `PerfectSecrecy.perfectlyIndistinguishable`
proof in plain mathematical language (see
`KatzLindell/perfect-secrecy-iff-indistinguishable.pdf`), the natural
human-readable argument is phrased entirely in terms of conditional
probability (`Pr[guess(C) = 1 | B = 1]`, independence of the key and the
challenge bit, etc.). The actual Lean proof never uses that vocabulary — it
achieves the same result through direct `tsum` algebra (`PMF.bind_apply` +
a hand-written `swap_sum` lemma for reordering nested sums). The two proofs
are doing the same work, but the Lean one has no way to *say* "conditional
probability" even though that's the natural way a human would describe it.

## Possible project

A `PMF`-native conditional probability API — either:

- a `PMF.cond : PMF α → Set α → PMF α` defined directly (not by round-tripping
  through `Measure`), with simp lemmas relating it to `bind`/`pure`/`tsum` the
  same way the rest of the `PMF` API works, or
- at minimum, simp lemmas bridging `(PMF.toMeasure p)[|s]` back to a `PMF`
  (when the conditioning event has positive probability) and relating its
  `PMF.toMeasure`-level probabilities to concrete sums,

would make discrete-probability crypto/CS proofs (this kind of
indistinguishability game is a very common pattern) much more readable and
closer to how they're written on paper, instead of requiring an indirect
"Shannon-style ciphertext distribution equality" reformulation (as
`PerfectSecrecy` does here) specifically to dodge conditional probability.

This seems like a reasonably self-contained, well-scoped upstream Mathlib
contribution if anyone wants to pick it up — has not been attempted or
scoped out further here.

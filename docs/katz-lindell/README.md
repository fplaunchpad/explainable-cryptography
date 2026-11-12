# Katz–Lindell perfect secrecy

Supporting material for `ExplainableCrypto/KatzLindell/`, which formalizes
Definitions 2.3 and 2.6 and Exercise 2.6 of Katz and Lindell,
*Introduction to Modern Cryptography* (perfect secrecy, perfect
indistinguishability, and their equivalence).

- [`perfect-secrecy-iff-indistinguishable.pdf`](perfect-secrecy-iff-indistinguishable.pdf) —
  a natural-language, step-by-step account of the equivalence proof, with
  each step cited against the corresponding Lean theorem
  (`privKeav_eq`, `PerfectSecrecy.perfectlyIndistinguishable`,
  `PerfectlyIndistinguishable.perfectSecrecy`,
  `perfectSecrecy_iff_perfectlyIndistinguishable`).
- [`pmf-conditional-probability-gap.md`](pmf-conditional-probability-gap.md) —
  an observation made while writing the proof up: Mathlib has no convenient
  bridge from `PMF` to its general `ProbabilityTheory.cond` conditional
  probability API, which forces proofs like this one to work with
  unconditioned `tsum` arithmetic instead of the conditional-probability
  phrasing a human would use on paper. Flagged as a possible self-contained
  upstream Mathlib contribution; not attempted here.

This module is independent of `ExplainableCrypto/OneTimePad/`, which proves
perfect secrecy for one concrete finite cipher directly, without building
an adversarial indistinguishability game or this general equivalence.

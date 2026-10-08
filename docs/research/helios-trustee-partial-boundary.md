# Trustee partials against initial public recipes

Current status (2026-09-11): [B8 is complete](helios-published-static-equivalence.md).
The full partial/final-frame static-equivalence theorems discharge the binding
and local-induction premises left open in this record's historical checkpoint.
B9 process matching and B10 labelled bisimilarity remain open.

Status: **machine-checked boundary theorems**. This is progress within B8 of the
[proof blueprint](helios-proof-blueprint.md). Static equivalence of the complete
[partial frame](helios-published-frames.md) remains open.

## What the boundary theorem says

`initial_trustee_partial_match_iff` characterizes decryption of any public
initial recipe `r` using `partialDecrypt(secret, binding)`. If `binding` is
E-equal to an election-key ciphertext, a decryption match exists exactly when
`eval r` is E-equal to the complete binding. The premise includes the
ciphertext's key, nonce and plaintext; equality of plaintexts alone is
insufficient. The theorem permits arbitrary ground binding components,
positive candidate counts and valid ground candidate substitutions. It uses
the full restricted-name policy and does not require fresh names.

The proof retains both decryption rules of the unsorted model:

- E5 could use the partial itself as an ordinary secret. Minimum public-key
  origins and initial partial non-deducibility exclude an initial public key
  equal to `pk(partialDecrypt(secret, binding))`. Minimum ciphertext grouping
  then excludes any initial public ciphertext with that key.
- E6 succeeds precisely when its whole binding agrees with the supplied
  ciphertext. Constructor injectivity recovers this equality from a match.

The E5 exclusion is specific to the initial historical frame. A public recipe
can construct a ciphertext under `pk(partial)` after publication and decrypt
it using E5. The checked control `public_new_cipher_decrypts` exhibits this
behavior in the actual four-handle partial frame.

## Connection to the accepted election

`accepted_tally_partial_match_iff` discharges the ciphertext-shape premise
using accepted-sequence reconstruction. It assumes fresh names, public
submissions, and chronological acceptance from the two-honest-ballot board
in the false world. For every candidate, both assignments and every initial
public recipe, a match exists exactly at the actual aggregate ciphertext.

`accepted_tally_partial_match_swap` transfers this condition using B7 and the
public tally recipe. `accepted_tally_partial_decryption_value` identifies the
result with the actual tally result. `accepted_tally_partial_probe_numeric`
applies this to the real partial-frame probe: decrypt the candidate's partial
projection against a lifted initial recipe. If the false-world probe matches,
both worlds yield the same numeral, bounded by the number of submissions plus
two. The match premise is explicit; unsuccessful probes are not claimed to
return a numeral.

`tally_partial_eq_iff` reduces equality between candidate partials to equality
between their full bindings. `tally_partial_equality_swap` transfers that
equality pattern through B7 for public submissions and fresh names, without
requiring acceptance.

These results do not yet classify arbitrary recipes over the new partial
handles. Such recipes can nest new keys, ciphertexts, partials and destructors.
B8 still requires equality preservation and reflection for every pair of
public recipes in that extended frame. B9 process matching and B10 symbolic
secrecy also remain open.

## Evidence and controls

Artifacts:

- [Boundary theorems](../../ExplainableCrypto/Helios/Symbolic/TrusteePartialBoundary.lean).
- [Eight SPOTs](../../ExplainableCrypto/Helios/Symbolic/TrusteePartialSPOT.lean).
- [Executable gate](../../ExplainableCrypto/Helios/Symbolic/TrusteePartialExperiments.lean).

The controls cover both candidate matches and independent zero/one results,
wrong-candidate rejection, unequal partial slots in both worlds, exclusion of
an initial partial-keyed ciphertext, newly constructed E5 ciphertexts with
arbitrary payloads, an actual public E5 probe, a delayed nonliteral initial
recipe, and the necessity of the secret-name restriction.

The gate first detects ignoring E6 binding and omitting structured-key E5 at
input 0, seed 1, zero shrinks. Seeds 1, 7 and 42 each pass 500 cases, size 40,
`gaveUp=0`; 2048 deterministic inputs pass. The generated scope is two
candidates with nonliteral values, both assignments, matching and wrong
candidate bindings, and newly constructed ciphertexts with varied public
nonces and payloads. Log: `tmp/variable-overlap/trustee-partial-gate.log`
(1002 jobs). Raw normalization serves only this executable test scope; the
full-E claims come from the checked theorems.

The trusted protocol equations remain E5/E6 in `Rewriting.lean`, corresponding
to the whole-ciphertext binding in the historical source. No cryptographic
implementation or computational-security claim is introduced.

Full `lake build` passes **3620 jobs**. The audit covers **1812 nonempty
standard-only axiom reports**, **20 axiom-free reports**, **846 public theorem
entries** and **47 current-status documents**. Seventeen new theorem audits
include the eight controls. Log: `tmp/variable-overlap/trustee-partial-full-build.log`.
Initial failed checks were proof engineering: equality transport notation and
unfolding term publicness for decidable literal-name controls. The model and
candidate claim were unchanged.

[Expanded public decryption](helios-expanded-public-decryption.md) now closes
direct E5 and constructed-partial E6. The remaining local case is complete
borrowed trustee tally-binding transfer for minimum ciphertexts. B7 handles
retained old recipes; general nested new-handle binding remains unproved.

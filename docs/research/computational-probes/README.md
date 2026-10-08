# Computational library validation

VCVio is selected. The source and evidence discussion is in the
[results ledger](../helios-results.md#concrete-computational-library-validation-2026-09-12-in-progress).
These probes are prerequisites, not Helios privacy proofs.

| Probe | Checked interface |
|---|---|
| `VCVioInterfaces.lean` | ElGamal correctness and DDH reduction, Sigma extraction interface, structural query bound, Fiat–Shamir completeness |
| `CatCryptInterfaces.lean` | ElGamal and Chaum–Pedersen theorem audits; proved `GroupParam` to `CyclicGroup` adapter and explicit exponentiation equality |
| `VCVioGame.lean` | Adaptive probabilistic callback, list board state, observable rejection, exact probabilities and state updates |
| `CatCryptGame.lean` | The same acceptance experiment using a typed private heap and a callback isolated from that heap |

Both games use two public tokens. Replay acceptance is 1 without weeding and 0
with weeding; fresh adaptive input is accepted with probability 1; blind fixed
input is accepted with probability 1/2. These are exact library-semantic
probabilities. The tokens are not encrypted ballots. The two state representations
are checked independently; no cross-framework equivalence theorem is claimed.

VCVio's native version is Lean 4.33.1, revision
`6d5c7d502ad97f676293a84c3d364c518cbde117`. CatCrypt's is Lean 4.30.0,
revision `91410d23b34a886fcc35765d59a93565906bbe17`.
Archive copies were created in `tmp/concrete-helios/` with `git archive HEAD`,
preserving upstream tracked checkouts and using each committed manifest.
Install the two pinned toolchains with `elan toolchain install`, then run
`lake exe cache get` in each copy **sequentially**: the Mathlib cache clients
share a curl configuration file and collided when run simultaneously.

From the VCVio archive directory:

```sh
lake build Examples.ElGamal.Basic VCVio.CryptoFoundations.SigmaProtocol Examples.ElGamal.ComputationalComplexity VCVio.CryptoFoundations.FiatShamir.Sigma
lake env lean ../../../docs/research/computational-probes/VCVioInterfaces.lean
lake env lean ../../../docs/research/computational-probes/VCVioGame.lean
```

From the CatCrypt archive directory:

```sh
lake build CatCryptCore.Examples.ElGamalDDH CatCryptCore.Examples.ChaumPedersen
lake env lean ../../../docs/research/computational-probes/CatCryptInterfaces.lean
lake env lean ../../../docs/research/computational-probes/CatCryptGame.lean
```

Final probe logs are in `tmp/concrete-helios/{vcvio,catcrypt}-{interfaces,game}.log`;
the extended VCVio audit also runs in the selected package and is recorded in
`selected-interfaces.log`. All reported axioms are standard Lean axioms. The
CatCrypt dependency build has existing linter warnings; the final local probes
have none. This is a selected-module audit, not an audit of every upstream theorem.

The [VCVio paper](https://eprint.iacr.org/2026/899), especially Appendix D,
describes the efficiency-parametric security interface. Its existence does not
prove that our eventual reduction is polynomial time. The pinned source also
exposes a stricter backend-relative complexity interface; backend adequacy and
the actual reduction's implementation/cost remain obligations.

After the toolchain migration, VCVio probes also run directly from the root:

```sh
lake env lean docs/research/computational-probes/VCVioInterfaces.lean
lake env lean docs/research/computational-probes/VCVioGame.lean
```

The main development now shares Lean/Mathlib 4.33.1 and the pinned VCVio
dependency. CatCrypt remains an isolated comparison on its original toolchain;
its source and pins are unchanged.


Current source inspection for the local-cost obligation (2026-09-13): the pinned
`VCVioComplexity/README.md` and `Backend/TuringMachine.lean` explicitly leave
general machine composition and oracle-machine adequacy open. The optional
package's individual machine canaries are not a general PPT backend; the root
ElGamal complexity example proves structural query accounting and semantic closing,
with local quantitative operations still future work. No new optional-package
build, dependency or compatibility repair is claimed here. The results ledger
records the narrow finite-cache implementation/correspondence work undertaken
while preserving those upstream pins.

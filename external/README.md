# Upstream formal-methods libraries

These Git submodules preserve the source revisions used in the
[Helios library analysis](../docs/research/helios-library-analysis.md).
The [process and symbolic library exploration](../docs/research/helios-reuse-source-exploration.md)
records the additional references and their exact pins for the post-B reuse audit.

| Submodule | Upstream | Lean |
| --- | --- | --- |
| `LeanDY` | https://github.com/SecPriv/leandy | 4.24.0-rc1 |
| `VCVio` | https://github.com/Verified-zkEVM/VCVio | 4.33.1 |
| `CatCrypt-core` | https://github.com/spitters/CatCrypt-core | 4.30.0 |
| `CSLib` | https://github.com/leanprover/cslib | 4.34.0-rc2 |
| `SymbolicCryptographyLean` | https://github.com/ravst/SymbolicCryptographyLean | 4.20.0-rc5 |
| `Isabelle-AFP` | https://github.com/isabelle-prover/mirror-afp-devel | Isabelle development AFP; `HOL-Nominal` session parent |

To fetch the pinned sources after cloning this repository:

```sh
git submodule update --init
```

`Isabelle-AFP` is the Git mirror of the Mercurial AFP development repository.
It contains the `Psi_Calculi` and `Pi_Calculus` sessions. Its initial local
checkout is shallow and sparse to limit download size. The Git pin is portable;
the local sparse-checkout configuration is not stored in the parent repository.
After initializing it, the same working-tree selection can be configured with:

```sh
git -C external/Isabelle-AFP sparse-checkout set thys/Psi_Calculi thys/Pi_Calculus metadata/entries
```

This is a source-inspection selection, not a complete Isabelle build setup.
To populate the full pinned archive, run
`git -C external/Isabelle-AFP sparse-checkout disable`.

The main Lean project builds independently of these checkouts. If we adopt a
library, it should become a separately pinned dependency in `lakefile.toml`;
the source comparison checkouts do not establish Lean import paths.

To inspect revisions and local modifications:

```sh
git submodule status
git submodule foreach 'git status --short'
```

Update a submodule deliberately by fetching upstream and checking out the chosen
commit inside that directory. Review the changes, update the research notes and
toolchain information, then stage the submodule path in the parent repository.
Normal `git submodule update --init` restores recorded revisions rather than
following the latest upstream branch.

The checkouts retain their upstream licences. Optional nested native-backend
submodules are not needed for this source comparison or the main demo build.

The root MIT license does not relicense these third-party repositories.

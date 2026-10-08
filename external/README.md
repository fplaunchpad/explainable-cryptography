# Upstream security libraries

These Git submodules preserve the source revisions used in the
[Helios library analysis](../docs/research/helios-library-analysis.md).

| Submodule | Upstream | Lean |
| --- | --- | --- |
| `LeanDY` | https://github.com/SecPriv/leandy | 4.24.0-rc1 |
| `VCVio` | https://github.com/Verified-zkEVM/VCVio | 4.33.1 |
| `CatCrypt-core` | https://github.com/spitters/CatCrypt-core | 4.30.0 |

To fetch the pinned sources after cloning this repository:

```sh
git submodule update --init
```

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

## Licenses

These reference repositories retain their upstream licenses at the pinned revisions:

| Reference | License |
| --- | --- |
| [VCVio](VCVio/LICENSE) | Apache-2.0 |
| [LeanDY](LeanDY/LICENSE) | LGPL-3.0 |
| [CatCrypt-core](CatCrypt-core/LICENSE) | MIT |

They are not covered by the root MIT license.

# Repair target: unresolved concrete semantics

Status: specified source discrepancy; no complete concrete repair theorem.

Cortier–Smyth's [author preprint](https://publications.bensmyth.com/2012-attacking-ballot-secrecy-in-Helios/)
§4.1 combines ballot weeding with assumptions about non-malleable signatures of
knowledge and decryption restricted to ciphertexts `(a,b)` with both coordinates
in `Z_p*`. Membership in that multiplicative group permits 1. Thus this condition
alone does not exclude the neutral ciphertext `(1,1)`. Unique representation of
group elements also does not remove the group's identity. This observation does
not by itself refute a theorem with additional cryptographic assumptions.

Smyth's [Replay attacks that violate ballot secrecy in Helios](https://publications.bensmyth.com/files/Smyth12a-attacking-Helios.pdf),
§4, pp. 11–12, identifies the missing multiplication by `(1,1)` in the earlier
symbolic model. The paper distinguishes sound symbolic analysis from incomplete
coverage of concrete ElGamal operations. It discusses stronger cryptographic
constructions and possible changes to proof weeding; these are separate targets,
not an implicit interpretation of ciphertext-component weeding.

The local supplementary paper is `_references/smyth-2012-replay-attacks-helios.pdf`
(May 2012). It predates the August 2012 journal author preprint held locally as
`cortier-smyth-2013-attacking-and-fixing-helios.pdf`; it should not be described
as a subsequent correction of that exact journal version. No authoritative
correction fixing the precise domain condition has been established here.

## Consequence for this repository

The finite [attack model](helios-model.md) has opaque ciphertext handles and
ideal certificates. It represents copying and permutation, and deliberately
has no group multiplication operation or neutral ciphertext. Its component
checks block those two witnesses. This is evidence about those witnesses only.

The agreed order is:

1. Reproduce the historical symbolic theorem with the paper's term algebra,
   adversary and process semantics, explicitly retaining its abstraction limits.
2. Specify a concrete cryptographic variant and its proof assumptions first,
   then model the additional attacks and prove the chosen variant's security.

The first phase focuses on the historical symbolic explanation.
The second phase needs a precise protocol choice; adding a nonidentity test on our own
would not establish that it is a sufficient or faithful repair.

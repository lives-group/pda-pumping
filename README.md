# The Pumping Lemma for Context-Free Languages, via Pushdown Automata

An Agda formalization of the pumping lemma for context-free languages, proved by
the pushdown-automaton route rather than the classical parse-tree route.

The theorem is stated directly about the empty-stack language of an _arbitrary_
pushdown automaton, and never mentions grammars in hypothesis or conclusion.
Every witness is computed: the pumping length, the five-part factorization, and,
for each `k`, an accepting computation of the pumped word.

## Layout

```
.
├── flake.nix              Nix build for both the paper and the formalization
├── flake.lock             pinned to nixos-25.05 (Agda 2.7.0.1, stdlib 2.2)
├── pda-pumping.agda-lib   Agda library file: include: src
├── src/                   the formalization, 22 modules, ~2,750 lines
│   ├── CFG/Base.agda          the Finite record: a listing plus exhaustiveness
│   ├── Utils/                 AllDistinct, Fin, Finite, Maybe, Nat helpers
│   └── PDA/
│       ├── Base.agda          the PDA record and its step relation
│       ├── Language.agda      acceptance by empty stack
│       ├── Normal.agda        the ±1 normal form
│       ├── Trace.agda         surgery on computations
│       ├── NormalizePDA.agda  arbitrary PDA → normal PDA, language-exact
│       └── Pumping/           the geometric argument and the two theorems
└── paper/
    ├── paper.tex          the paper (18 pages, LNCS)
    ├── references.bib
    ├── llncs.cls          Springer LNCS class
    └── splncs04.bst       Springer LNCS bibliography style
```

The entry point of the development is `src/PDA/Pumping/Arbitrary.agda`, whose
last definition is `pumping-pda`, the end-to-end theorem. Type-checking that one
module pulls in the other 21.

Two theorems live there:

- `pda-pumping-N` — the pumping lemma for an automaton already in ±1 normal
  form;
- `pumping-pda` — the same statement for an arbitrary PDA, obtained by composing
  the normalization with the previous theorem.

## Building with Nix

The flake pins nixpkgs to `nixos-25.05`, which ships the exact pair the
development was checked against: **Agda 2.7.0.1** and **standard-library 2.2**.
Newer channels already carry Agda 2.8 and standard-library 2.3, which the
development has not been checked against.

```sh
nix build .#paper           # produces result/paper.pdf
nix build .#formalization   # type-checks src/, takes about 20 minutes
nix develop                 # a shell with Agda, the stdlib and TeX Live
```

`nix flake check` runs both, but it also evaluates the outputs for every
supported system, so on a single machine

```sh
nix build .#paper .#formalization
```

is the faster equivalent.

The two derivations depend only on their own sources: editing the paper does not
invalidate the Agda type-check, and running `pdflatex` locally does not
invalidate the Nix build of the PDF.

## Building without Nix

**The formalization** needs Agda 2.7.0.1 and standard-library 2.2 registered
under the name `standard-library-2.2` (the name `pda-pumping.agda-lib` depends
on). From the repository root:

```sh
agda src/PDA/Pumping/Arbitrary.agda
```

Expect roughly twenty minutes on a current machine. Cost is concentrated in
`PDA/Pumping/CaseHighCore.agda`, whose reconstruction elaborates deeply nested
dependent records.

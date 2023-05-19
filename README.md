# A Higher-Order Lean 4 Hammer

*Note: Still in early stages of development!*

This repo adds a hammer tactic for Lean 4.
```lean
import HoSmt
set_option HoSmt.cvc5 "./bin/cvc5" -- You need to download CVC5 yourself.

theorem hello : ∀x : Nat, x * 0 = 0
  := by smt [Nat.mul_zero]
```

## How it works

Hammers have three stages:
1. *Lemma Selection*: Select roughly 1000 as-relevant-as-possible helper lemmas for the
   problem (i.e. Lean proof goal) we're trying to solve.
2. *Translation*: Translate proof goal and helper lemmas from Lean to a language that the
   SMT solver will understand.
   Lean is built on Martin-Löf type theory and the calculus of inductive constructions,
   whereas SMT solvers usually want non-polymorphic first or higher order logic.
   Types are converted to simple types in roughly two steps:
   1. *Type index erasure*: For example replacing `Vec α len` with a subtype
      `{ v : VecE α // VecG α len v }`, where `VecE` is the index-erased type, and `VecG` is a guarding predice which enforces the length of `v`.
   2. *Monomorphization*: For example occurences of `List Nat` are replaced with `ListNat`.
3. *Proof Reconstruction*: Running the SMT solver (such as CVC5) produces a proof for
   the translated (HOL) problem, from which we need to create a proof for the original
   MLTT+CIC problem.

So far, this repo implements an (admittedly buggy) translation from MLTT+CIC to non-polymorphic HOL.

## Setting up CVC5

You can obtain CVC5 from [CVC5's GitHub Releases][cvc5].
Tested with CVC5 1.0.2 macOS arm64.
For some reason the newest version (1.0.5) doesn't like TPTP.
```lean
set_option HoSmt.cvc5 "./bin/cvc5"
```

## Documents
This project originates from a *science internship* (in German: Praxis der Forschung) at
[KIT](https://kit.edu/).
There is a ["paper"](doc/2023-05-17%20Paper.pdf) describing the techniques used,
as well as providing tons of references.
There also is a [presentation](doc/2023-06-15%20Final%20Presentation.pdf).

## Misc

### Other Options

The default timeout is 3 seconds.
You can customize that with
```lean
set_option HoSmt.time 10
```

### Folder Structure
```
Lean-HoSmt/         Repo root (open in VSCode, run `lake build` here, etc).
    lakefile.lean       Project manifest used by `lake`.
    HoSmt.lean          "Root source file" defining the `smt` tactic.
    HoSmt/              Source files.
    ...
```

[cvc5]: https://github.com/cvc5/cvc5/releases/tag/cvc5-1.0.2
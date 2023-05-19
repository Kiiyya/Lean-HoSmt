# A Higher-Order Lean 4 Hammer

*Note: Still in early stages of development!*

This repo adds a hammer tactic for Lean 4.
```lean
import HoSmt
set_option HoSmt.cvc5Cmd "./bin/cvc5" -- You need to download CVC5 yourself.

theorem hello : ∀x : Nat, x * 0 = 0
  := by smt [Nat.mul_zero]
```

So far, this repo implements an (admittedly buggy) translation from MLTT+CIC to non-polymorphic HOL.

## How it works

Hammers have three stages:
1. *Lemma Selection*: Select roughly 1000 as-relevant-as-possible helper lemmas for the
   problem (i.e. Lean proof goal) we're trying to solve.
2. *Translation*: Translate proof goal and helper lemmas from Lean to a language that the
   SMT solver will understand.
   Lean is built on Martin-Löf type theory (MLTT) and the calculus of inductive constructions (CIC),
   whereas SMT solvers usually want non-polymorphic first or higher order logic.
   Types are converted to simple types in roughly two steps:
   1. *Type index erasure*: For example replacing `Vec α len` with a subtype
      `{ v : VecE α // VecG α len v }`, where `VecE` is the index-erased type, and `VecG` is a guarding predice which enforces the length of `v`.
   2. *Monomorphization*: For example occurences of `List Nat` are replaced with `ListNat`.
3. *Proof Reconstruction*: Running the SMT solver (such as CVC5) produces a proof for
   the translated (HOL) problem, from which we need to create a proof for the original
   MLTT+CIC problem.


## Setting up CVC5

You can obtain CVC5 from [CVC5's GitHub Releases][cvc5].
Tested with CVC5 1.0.2 macOS arm64.
For some reason the newest version (1.0.5) doesn't like TPTP.
You can then set the path to the binary via for example:
```lean
set_option HoSmt.cvc5Cmd "./bin/cvc5"
```

## Other Options

The default timeout is 3 seconds.
You can customize that with
```lean
set_option HoSmt.time 10
```

## Folder Structure
```
Lean-HoSmt/         Repo root (open in VSCode, run `lake build` here, etc).
    lakefile.lean       Project manifest used by `lake`.
    HoSmt.lean          "Root source file" defining the `smt` tactic.
    HoSmt/              Source files.
    ...
```

[cvc5]: https://github.com/cvc5/cvc5/releases/tag/cvc5-1.0.2

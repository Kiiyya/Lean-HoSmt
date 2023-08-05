--! Handles IO, invoking SMT commands, environment variables.
import Lean
import Lean.Data.Options
import HoSmt.Options

namespace HoSmt.System

open IO.Process IO.FS Lean

/-- Pipe input into stdin of the spawned process, then return output upon completion. -/
def cmd_with_stdin (args : SpawnArgs) (input : String) : IO Output := do
  let child <- spawn { args with stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) <- child.takeStdin
  stdin.putStr input
  stdin.flush
  let stdout <- IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr <- child.stderr.readToEnd
  let exitCode <- child.wait
  let stdout <- IO.ofExcept stdout.get
  return { exitCode, stdout, stderr }

/-- Run CVC5 on the input. Timeout is in seconds, defaults to 3. -/
def cmd_cvc5 [Monad m] [MonadOptions m] [MonadLiftT IO m] (input : String) : m Output := do
  let cmd := HoSmt.cvc5.get (<- getOptions)
  let timeout := HoSmt.time.get (<- getOptions)
  cmd_with_stdin {
    cmd := cmd,
    args := #[
      "--lang=tptp",
      "--output-lang=smt",
      "--dump-models",

      "--dump-proofs",
      "--proof-format-mode=alethe", -- https://cvc5.github.io/docs/cvc5-1.0.0/proofs/output_alethe.html
      "--dag-thresh=0", -- required as per cvc5 docs ^
      "--simplification=none", -- required as per cvc5 docs ^
      "--proof-granularity=theory-rewrite", -- required as per cvc5 docs ^

      s!"--tlimit={timeout * 1000}", -- milliseconds
      "--stats", -- give statistics on exit

      "--full-saturate-quant",
      
      -- Options which don't seem to hurt:
      -- "--quant-dsplit=agg",
      -- "--inst-when=full",
      -- "--trigger-sel=all",

      -- Bad Options: turning these on breaks things
      -- "--ho-elim=true",
      -- "--fmf-fun=true", -- "find models for recursively defined functions, assumes functions are admissible"
      -- "--fmf-fun-rlv=true",
      -- "--ext-rewrite-quant=true", -- bad: breaks working proofs
      "-"
    ]
  } input

/-- Invoke cvc5 with raw string input. More for debugging. -/
elab "#cvc5" s:str : command => do
  let some s := s.raw.isStrLit?
    | throwError "Expected a string literal"
  let result <- System.cmd_cvc5 s
  if result.exitCode == 0 then
    logInfo result.stdout
  else
    logError s!"{result.stdout} {result.stderr}"

section test
  /- Should produce:
  ```s
  unsat
  (assume a0 (not (forall ((X Bool)) (= X X))))
  (assume a1 true)
  (step t1 (cl (not (= (not (forall ((X Bool)) (= X X))) false)) (not (not (forall ((X Bool)) (= X X)))) false) :rule equiv_pos2)
  (step t2 (cl (= (not (forall ((X Bool)) (= X X))) false)) :rule undefined :args ((not (forall ((X Bool)) (= X X))) 7 12))
  (step t3 (cl) :rule resolution :premises (t1 t2 a0))
  ```
  
  `./cvc5-macOS-arm64-1.0.2 --version` gives me:
  ```t
  This is cvc5 version 1.0.2 [git tag 1.0.2 branch HEAD]
  compiled with GCC version Apple LLVM 13.0.0 (clang-1300.0.29.30)
  on Aug 26 2022 17:17:23
  ```
  -/
  -- set_option HoSmt.cvc5Cmd "./bin/cvc5-macOS-arm64-1.0.2" in
  -- #cvc5 "thf(c, conjecture, (![X : $o]: (X = X)))." -- works

  -- set_option HoSmt.cvc5Cmd "./bin/cvc5-macOS-arm64-1.0.5" in
  -- #cvc5 "thf(c, conjecture, (![X : $o]: (X = X)))." -- doesn't work for some reason :(
end test

/-- Run CVC5 on the input. Timeout is in seconds, defaults to 3. -/
def cmd_zipperposition [Monad m] [MonadOptions m] [MonadLiftT IO m] (input: String) : m Output := do
  let cmd := HoSmt.zipperposition.get (<- getOptions)
  cmd_with_stdin {
    cmd := cmd
    args := #["--input=tip"]
  } input

/-- Invoke cvc5 with raw string input. More for debugging. -/
elab "#zipper" s:str : command => do
  let some s := s.raw.isStrLit?
    | throwError "Expected a string literal"
  let result <- System.cmd_zipperposition s
  if result.exitCode == 0 then
    logInfo result.stdout
  else
    logError s!"{result.stdout} {result.stderr}"

end System
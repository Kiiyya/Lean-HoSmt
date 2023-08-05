import Lake
open Lake DSL

package HoSmt

require std from git "https://github.com/leanprover/std4"@"main"

require Duper from git "https://github.com/leanprover-community/duper"@"main"

-- Only needed for tests:
require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"

@[default_target]
lean_lib HoSmt

import Lake
open Lake DSL

package «syl_thm_env» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «SylThmEnv» {
  -- add any library configuration options here
}

import Lake
open Lake DSL

package «lean4-example» {
  -- add package configuration options here
}

@[default_target]
lean_lib «Lean4Example» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "a9a186c1be45e4f306d0d7649facfb59b17bd996"

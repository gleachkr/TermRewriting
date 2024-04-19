import Lake
open Lake DSL

package «TermRewriting»

require aesop from git "https://github.com/JLimperg/aesop"
require mathlib from git "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «TermRewriting»

import Lake
open Lake DSL

package «intro-to-cp» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.6.0-rc1"

lean_lib «IntroToCp» where
  -- add library configuration options here


@[default_target]
lean_exe «intro-to-cp» where
  root := `Main
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

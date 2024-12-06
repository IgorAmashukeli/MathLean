import Lake
open Lake DSL

package «header» where
  -- add package configuration options here

lean_lib «Header» where
  -- add library configuration options here

@[default_target]
lean_exe «header» where
  root := `Main

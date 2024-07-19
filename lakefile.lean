import Lake
open Lake DSL

package «mathematics» where
  -- add package configuration options here

lean_lib «Mathematics» where
  -- add library configuration options here

@[default_target]
lean_exe «mathematics» where
  root := `Main

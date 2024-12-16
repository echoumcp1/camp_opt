import Lake
open Lake DSL

package «final» where
  -- add package configuration options here

lean_lib «Final» where
  -- add library configuration options here

@[default_target]
lean_exe «final» where
  root := `Main

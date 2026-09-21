import Lake
open Lake DSL
package TuzaDelta8 where
@[default_target]
lean_lib TuzaDelta8
lean_exe tuza_delta8 where
  root := `Main

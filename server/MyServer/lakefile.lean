import Lake
open Lake DSL

package myServer {
  -- add package configuration options here
}

lean_lib Lib {

}

@[default_target]
lean_exe myServer {
  root := `Main
  supportInterpreter := true
}

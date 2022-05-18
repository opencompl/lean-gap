import Lake
open Lake DSL

package «GAP» {
  -- add configuration options here
  supportInterpreter := true
  libName := "GAP"
  binRoot := `GAP
  libRoots := #[`GAP] 
}

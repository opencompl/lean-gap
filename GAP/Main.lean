-- main entrypoint
import GAP.P
import GAP.Doc
import GAP.AST
import GAP.Group

open GAP.AST
open GAP.Doc
open GAP.P
open IO
open System


-- TOPLEVEL PARSER
-- ==============

-- https://github.com/leanprover/lean4/blob/master/tests/playground/file.lean
def main (xs: List String): IO Unit := do
  match xs with
  | [] =>  
      let _ <- GAP.Group.tests; return () -- run tests.
  | _ => do
    -- let path : System.FilePath :=  xs.head!
    let path :=  xs.head!
    let contents ← FS.readFile path;
    IO.eprintln "FILE\n====\n"
    IO.eprintln contents
    -- IO.eprintln "\nEDSL TESTING\n============\n"
    -- IO.eprintln MLIR.EDSL.opRgnAttr0
    IO.eprintln "PARSING\n=======\n" 
    let ns := []
    let (loc, ns, _, res) <-  (parse_toplevel ()).runP locbegin ns contents
    IO.eprintln (vgroup $ ns.map (note_add_file_content contents))
    IO.eprintln "done parsing...." 
    match res with
     | Result.ok op => do
       IO.println   "# ***Parse succeeded:***"
       IO.println $ vgroup $ op.map Pretty.doc
     | Result.err err => do
        IO.eprintln "***Parse Error:***"
        IO.eprintln (note_add_file_content contents err)
     | Result.debugfail err =>  do
        IO.eprintln "***Debug Error:***"
        IO.eprintln (note_add_file_content contents err)
     
  return ()

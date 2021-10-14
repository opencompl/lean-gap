-- main entrypoint
import GAP.P
import GAP.Doc
import GAP.AST
import GAP.Group
import GAP.Semantics

open GAP.AST
open GAP.Doc
open GAP.Semantics
open Pretty
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
    let notes := []
    let (loc, ns, _, res) <- (parse_toplevel ()).runP locbegin notes contents
    IO.eprintln (vgroup $ ns.map (note_add_file_content contents))
    IO.eprintln "done parsing...." 
    match res with
     | Result.ok stmts => do
       IO.println   "# ***Parse succeeded:***"
       IO.println $ vgroup $ stmts.map Pretty.doc
       IO.println   "# *** Executing program ***"
       let out := GAP.Semantics.execute_stmts init_env stmts
       match out with
       | Result.ok env =>  do
         IO.eprintln  "# *** Run Succeeded: ***"
         IO.eprintln $ doc env
       | Result.err err => do 
           IO.eprintln "# *** Run Failed: ***"
           IO.eprintln err
       | Result.debugfail err => do 
           IO.eprintln "# *** Run Debug failure: ***"
           IO.eprintln err
     | Result.err err => do
        IO.eprintln "***Parse Error:***"
        IO.eprintln (note_add_file_content contents err)
     | Result.debugfail err =>  do
        IO.eprintln "***Debug Error:***"
        IO.eprintln (note_add_file_content contents err)
     
  return ()

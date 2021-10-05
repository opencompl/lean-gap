import GAP.P
import GAP.Doc

open GAP.P
open GAP.Doc
open GAP.Doc.Pretty
namespace GAP.AST

  inductive binop_type
  | add: binop_type
  | sub: binop_type
  | mul: binop_type
  | div: binop_type
  | exp: binop_type
  | mod: binop_type
  | and: binop_type
  | or: binop_type
  | eq: binop_type
  | neq: binop_type
  | lt: binop_type
  | gt: binop_type

  mutual
  inductive Expr
  | expr_neg: Expr -> Expr
  | expr_range2: (first: Expr) -> (last: Expr) -> Expr
  | expr_range3: (first: Expr) -> (second: Expr) -> (last: Expr) -> Expr
  | expr_bool: Bool -> Expr
  | expr_fn_call: (name: String) -> (args: List Expr) -> Expr
  | expr_list_composition: (lhs: String) -> (rhs: Expr) -> Expr
  | expr_var: String -> Expr
  | expr_str: String -> Expr
  | expr_not: Expr -> Expr
  | expr_binop: Expr -> binop_type -> Expr -> Expr
  | expr_index: (arr: Expr) -> (ix: Expr) -> Expr
  | expr_list: (args: List Expr) -> Expr
  | expr_permutation: List (List Int) -> Expr
  -- | nested functions? x(
  | expr_fn_defn: (params: List String) -> (is_vararg?: Bool) -> (locals: List String) ->
        (body: List Stmt) -> Expr
  inductive Stmt 
  | stmt_assign: (lhs: Expr) -> (rhs: Expr) -> Stmt
  | stmt_procedure_call: (fn: Expr) -> (args: List Expr) -> Stmt
  | stmt_if: (cond: Expr)
     -> (then_: List Stmt)
     -> (elifs: List (Expr × List Stmt))
     -> (else_: Option (List Stmt)) -> Stmt
  | stmt_return: (e: Expr) -> Stmt
  | stmt_for: (iter: String) -> (rhs: Expr) -> (body: List Stmt) -> Stmt
  inductive Block
  | mk: (stmts: List Stmt) -> Block
  end
  -- TODO: add while

instance : Coe (List Stmt) Block where
   coe (xs: List Stmt) := Block.mk xs

 -- | a block is a sequence of statements.
 -- abbrev Block := List Stmt

mutual

  partial def pconsume_symbol (s: String): P Unit := perror "foo"
  partial def ppeek_keyword: P (Option String) := perror "foo"
  partial def pconsume_keyword (s: String) : P Unit := perror "foo"

  -- | cannot have a ppeek_symbol because one symbol can be a proper
  -- | prefix of another, so we are not sure how to tokenize!
  -- partial def ppeek_symbol: P (Option String) := perror "foo"
  partial def ppeek_symbol? (s: String): P Bool := perror "foo"
  partial def pconsume_symbol (s: String): P Unit := perror "foo"

  partial def ppeek_keyword? (s: String): P Bool := do
   match (<- ppeek_keyword) with
    | none => return false
    | some k' => return s == k'

  partial def parse_expr_logical (u: Unit): P Expr := do 
    let l <- parse_expr_compare u
    let kwd <- ppeek_ident
    match kwd with
    | some "and" => do
        let r <- parse_expr u
        return Expr.expr_binop l binop_type.and r
    | some "or" => do
        let r <- parse_expr u
        return Expr.expr_binop l binop_type.or r
    | _ => return l

  partial def parse_list_commas (u: Unit) : P Expr := do
    let args <- pintercalated '[' (parse_expr u) ',' ']'
    return  (Expr.expr_list args)

  partial  def parse_list_range2 (u: Unit) : P Expr := do
    pconsume '['
    let first <- parse_expr u
    pconsume_symbol ".."
    let last <- parse_expr u
    return Expr.expr_range2 first last

  partial  def parse_list_range3 (u: Unit) : P Expr := do
    pconsume '['
    let first <- parse_expr u
    pconsume_symbol ","
    let snd <- parse_expr u
    pconsume_symbol ".."
    let last <- parse_expr u
    return Expr.expr_range3 first snd last
  
 -- | TODO: refactor for better errors!
  partial def parse_list (u: Unit) : P Expr := do 
    por (parse_list_commas u) $ (parse_list_range2 u)
  
  partial def parse_permutation (u: Unit): P Expr := 
        perror "don't know how to parse permutation"

  partial def parse_expr_leaf (u: Unit) : P Expr := do
    match (<- ppeek_keyword) with
    | some "true" => do 
           pconsume_keyword "true"
           return (Expr.expr_bool true)
    | some "false" => do
           pconsume_keyword "false"
           return (Expr.expr_bool false)
    | some "not" => do
           pconsume_keyword "not"
           let e <- parse_expr u
           return Expr.expr_not e
    | some x => perror $ doc "unknown keyword: |" ++ doc x ++ doc "|"
    | none => 
       match (<- ppeek_ident) with
       | some ident => return Expr.expr_var ident
       | none => 
          if (<- ppeek_symbol? "[") then parse_list u
          else if (<- ppeek_keyword? "function") then parse_fn_defn u
          else if (<- ppeek_symbol? "(") then parse_permutation u
          else if (<- ppeek_symbol? "-") then do
             pconsume_symbol "-"
             let e <- parse_expr u
             return Expr.expr_neg e
          else do
            perror "unknown leaf expression"
           
    
  partial def parse_expr_index (u: Unit) : P Expr := do
     let arr <- parse_expr_leaf u
     if (<- ppeek? '[')
     then do 
       pconsume '[' 
       let ix <- parse_expr u
       pconsume ']'
       return Expr.expr_index arr ix
     else return arr
   
-- // expr ->
-- // expr_logical[and, or] ->
-- // expr_compare[>=, <=] ->
-- // expr_arith_add_sub[+, -] ->
-- // expr_arith_mul_div[*, /] -> 
-- // expr_exponential[^] ->
-- // expr_index["expr[index]"] ->
-- // expr_leaf

  partial def parse_arith_exponential (u: Unit) : P Expr := do
     let l <- parse_expr_index u
     if (<- ppeek? '^')
     then do
       pconsume '^'
       let r  <- parse_expr u
       return Expr.expr_binop l binop_type.exp r
     else return l


partial def parse_arith_mul_div (u: Unit) : P Expr := do
  let l <- parse_arith_exponential u
  match (<- ppeek) with
    | some '*' => do
         pconsume '*'
         let r <- parse_expr u
         return Expr.expr_binop l binop_type.mul r
    | some '/' => do
         pconsume '/'
         let r <- parse_expr u
         return Expr.expr_binop l binop_type.div r
    | _ => return l


partial def parse_arith_add_sub_mod (u: Unit) : P Expr := do
  let l <- parse_arith_mul_div u
  match (<- ppeek) with
    | some '+' => do
         pconsume '*'
         let r <- parse_expr u
         return Expr.expr_binop l binop_type.add r
    | some '-' => do
         pconsume '/'
         let r <- parse_expr u
         return Expr.expr_binop l binop_type.sub r
    | some 'm' => do
           match (<- ppeek_keyword? "mod") with
              | true => do
                  let r <- parse_expr u
                  return Expr.expr_binop l binop_type.mod r
              | false => return l
    | _ => return l

-- TODO: write a higher order function that generates this.
partial def parse_expr_compare (u: Unit) : P Expr := do
  let l <- parse_arith_add_sub_mod u
  if (<- ppeek_symbol? "=") then do
         pconsume_symbol "="
         let r <- parse_expr u
         return Expr.expr_binop l binop_type.eq r
  else if (<- ppeek_symbol? "<>") then do
         pconsume_symbol "<>"
         let r <- parse_expr u
         return Expr.expr_binop l binop_type.neq r
  else if (<- ppeek_symbol? "<") then do
         pconsume_symbol "<"
         let r <- parse_expr u
         return Expr.expr_binop l binop_type.lt r
  else if (<- ppeek_symbol? ">") then do
         pconsume_symbol ">"
         let r <- parse_expr u
         return Expr.expr_binop l binop_type.gt r
  else return l
 

partial def parse_var : P String := do
  let x <- pident
  return  x

--  | returns true/false based on whether varargs or not
partial def parse_fn_args (u: Unit) : P (List String × Bool) := do
  pconsume_symbol "("
  if (<- ppeek_symbol? ")")
  then (return [], false)
  else do
    -- <rest_args> = ", <arg>  [<rest_args> | ")"]
    -- | TODO: consider using ppeekstar!
    let rec p_rest_args (u: Unit): P (List String × Bool) := do
          pconsume ','
          if (<- ppeek_symbol? "...") 
          then do
              pconsume_symbol "..."
              pconsume_symbol ")"
              return ([], true)
          else do
            let x <- parse_var
            let (xs, varargs?) <- por (p_rest_args u) (psuccess ([], false))
            return (x::xs, varargs?)
    let x <- parse_var
    let (xs, varargs?) <- (p_rest_args u)
    return (x::xs, varargs?)
   
partial def parse_fn_locals (u: Unit) : P (List String) := do
  if (<- ppeek_keyword? "local") 
  then do
    pconsume_keyword "local"
    let xs <- ppeekstar ',' pident
    pconsume_symbol ";"
    return xs
  else return []
    
  
partial def parse_fn_defn (u: Unit) : P Expr := do
  pconsume_keyword "function"
  let (params, varargs?) <- parse_fn_args  u
  let locals <- parse_fn_locals u
  let stmts <- pmany0 (parse_stmt u)
  return Expr.expr_fn_defn params varargs? locals stmts



-- | stop? should only peek, not consume!
partial def parse_stmts (pstop?: P Bool) (u: Unit) : P (List Stmt) := do
   let stop? <- pstop?
   match stop? with
   | true => return []
   | false => do
        let s <- parse_stmt u
        let ss <- parse_stmts pstop? u
        return (s::ss)

partial def whileM [Monad m] (cond: m Bool) (body: m a): m (List a) := do 
   if (<- cond)
   then do let a <- body; let as <- whileM cond body; return (a::as)
   else return []



-- | parse the else clause of an if then else
 partial def pelse (u: Unit)  : P  ((List (Expr × List Stmt)) × Option (List Stmt)) := do
   match (<- ppeek_keyword) with
      -- | some "elif" => do
      --        let cond <- parse_expr u
      --        pconsume_keyword "then"
      --        let body <- parse_stmts p_is_fi_or_elif_or_else u
      --        let (elifs, else_) <- pelse u
      --        return ((cond,body)::elifs, else_)
      -- | some "else" =>  do
      --     pconsume_keyword "else"
      --     let stmts <- parse_stmts (ppeek_keyword? "fi") u
      --     pconsume_keyword "fi"
      --     return ([], Option.some stmts)
      -- | some "fi" => 
      --   pconsume_keyword "fi"
      --   return ([], Option.none)
      | _ => perror "expected elif/else/fi at end of if"


partial def parse_if (u: Unit) : P Stmt := do
  let p_is_fi_or_elif_or_else : P Bool :=
     por (ppeek_keyword? "fi") (por (ppeek_keyword? "elif") (ppeek_keyword? "else"))
  pconsume_keyword "if"
  let cond <- parse_expr u
  pconsume_keyword "then"
  let body <- parse_stmts p_is_fi_or_elif_or_else u
  let (elifs, else_) <- pelse u
  return Stmt.stmt_if cond body elifs else_


partial def parse_assgn_or_procedure_call (u: Unit) : P Stmt := do
   let lhs <- parse_expr u
   if (<- ppeek_symbol? "(") then do
     let args <- pintercalated '(' (parse_expr u) ',' ')'
     return Stmt.stmt_procedure_call lhs args
   else if (<- ppeek_symbol? ":=") then do
     pconsume_symbol ":="
     let rhs <- parse_expr u
     return Stmt.stmt_assign lhs rhs
   else perror "expected assignment with := or function call with (...) at toplevel"

  

partial def parse_for(u: Unit): P Stmt := do
  pconsume_keyword "for"
  let var <- pident
  pconsume_keyword "in"
  let e <- parse_expr u
  pconsume_keyword "do"
  let body <- parse_stmts (ppeek_keyword? "od") u
  return Stmt.stmt_for var e body

  partial def parse_stmt (u: Unit) : P Stmt := do
  match (<- ppeek_keyword) with
  | some "if" => parse_if u
  | some "for" => parse_for u
  | _ => parse_assgn_or_procedure_call u


  -- | note to self: these give *worse* error messages!
  partial def parse_expr (u: Unit): P Expr := parse_expr_logical u

  end

partial def parse_toplevel (u: Unit): P (List Stmt) :=
  pmany1 (parse_stmt u)



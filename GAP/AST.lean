import GAP.P
import GAP.Doc

-- | no non-determinism for us!
open GAP.P hiding por pmany0 pmany1
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

instance : Pretty binop_type where
  doc (bop: binop_type) := 
    match bop with
    | binop_type.add => "+"
    | binop_type.sub => "-"
    | binop_type.mul => "*"
    | binop_type.div => "/"
    | binop_type.exp => "^"
    | binop_type.mod => "%"
    | binop_type.and => "and"
    | binop_type.or => "or"
    | binop_type.eq => "="
    | binop_type.neq => "<>"
    | binop_type.lt => "<"
    | binop_type.gt => ">"
mutual
  inductive Expr
  | expr_neg: Expr -> Expr
  | expr_range2: (first: Expr) -> (last: Expr) -> Expr
  | expr_range3: (first: Expr) -> (second: Expr) -> (last: Expr) -> Expr
  | expr_bool: Bool -> Expr
  | expr_num: Int -> Expr
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

mutual
  partial def expr_to_doc (e: Expr): Doc := 
    match e with
    | Expr.expr_neg f => "-" ++ expr_to_doc f
    | Expr.expr_range2  a z => 
        "[" ++ expr_to_doc a ++ ".." ++ expr_to_doc z
    | Expr.expr_range3 a b z =>
        "[" ++ expr_to_doc a ++ ", " ++ expr_to_doc b ++ ".." ++ expr_to_doc z 
    | Expr.expr_bool b => if b then "true" else "false"
    | Expr.expr_num i => doc i
    | Expr.expr_fn_call f xs =>
        let doc_xs := intercalate_doc (List.map expr_to_doc xs) ", " 
        f ++ "(" ++  doc_xs ++ ")"
    | Expr.expr_list_composition lhs rhs =>
        lhs ++ "{" ++ expr_to_doc rhs ++ "}" -- TODO: vgroup?
    | Expr.expr_var v => v
    | Expr.expr_str s => "\"" ++ s ++ "\""
    | Expr.expr_not x => "not(" ++ expr_to_doc x ++ ")"
    | Expr.expr_binop x op y => 
      expr_to_doc x ++ " " ++ doc op ++ " " ++ expr_to_doc y
    | Expr.expr_index arr ix => 
      expr_to_doc arr ++ "[" ++ expr_to_doc ix ++ "]"
    | Expr.expr_list args => 
      "[" ++ intercalate_doc (args.map expr_to_doc) ", " ++ "]"
    | Expr.expr_permutation cycles => 
      let doc_cycles := 
        cycles.map (fun c => "(" ++ intercalate_doc c ", " ++ ")")
      String.join doc_cycles
    | Expr.expr_fn_defn args vararg? locals body =>
      let doc_args := intercalate_doc args ", "
      let doc_vararg := (if args.isEmpty then "" else ", ") ++ 
                        (if vararg? then "..." else ".")
      let doc_locals : Doc := 
        if locals.isEmpty then "" 
        else "local " ++ intercalate_doc locals ", "
    
      vgroup ["function (" ++ doc_args ++ doc_vararg ++ ")",
              nest_vgroup $ [doc_locals] ++ (body.map stmt_to_doc)]

  partial def stmt_to_doc(s: Stmt): Doc := 
    match s with
    | Stmt.stmt_assign lhs rhs =>
      expr_to_doc lhs ++ " := " ++ expr_to_doc rhs
    | Stmt.stmt_procedure_call fn args => 
        let doc_args := intercalate_doc (args.map expr_to_doc) ", "
        expr_to_doc fn ++ "(" ++ doc_args ++ ")" ++ ";"
    | Stmt.stmt_if cond then_ elifs else_ =>
      let docs_if : List Doc := 
        ["if " ++ expr_to_doc cond ++ " then", nest_vgroup $ then_.map stmt_to_doc] 
      let docs_elifs : List Doc :=
        List.join ∘ elifs.map $
          (fun (cond, body) => 
            ["elif " ++ expr_to_doc cond,
             nest_vgroup $ body.map stmt_to_doc]) 
      let docs_else : List Doc := 
        match else_ with 
        | some else_ => ["else", nest_vgroup $ else_.map stmt_to_doc]
        | none => []      
      vgroup $  docs_if ++ docs_elifs ++ docs_else ++ [doc "fi;"]
    | Stmt.stmt_return e => "return " ++ expr_to_doc e ++ ";"
    | Stmt.stmt_for lhs rhs body =>
        vgroup ["for" ++ lhs ++ " in " ++ expr_to_doc rhs,
                nest_vgroup $ body.map stmt_to_doc, doc "od;"]  
end

instance : Pretty Expr where
  doc := expr_to_doc 

instance : Pretty Stmt where
  doc := stmt_to_doc 

def keywords : List String := 
  ["if", "then", "elif", "else", "fi"
   , "do", "od"
   , "for"
   , "true", "false"
   , "and", "or", "not"
   , "function", "return", "end"
   , "local"]

mutual



  -- | cannot have a ppeek_symbol because one symbol can be a proper
  -- | prefix of another, so we are not sure how to tokenize!
  -- partial def ppeek_symbol: P (Option String) := perror "foo"
  
  -- | TODO: rewrite using low level API?
  partial def pkwd? (s: String): P Bool := do
   if not $ keywords.contains s then do
     pdebugfail $ "can only peek  keywords, |" ++ s ++ "| is not keyword."
   else psym? s -- TODO, HACK: this reuses symbol. 

  partial def pkwd! (s: String) : P Unit := do
   if not $ keywords.contains s then do
     pdebugfail $ "can only peek  keywords, |" ++ s ++ "| is not keyword."
   else psym! s -- TODO, HACK: this reuses symbol.
  
  partial def pvar!: P String := do
    let x <- pident!
    if keywords.contains x then do 
    perror $ "expected variable, found keyword: |" ++ x ++ "|"
    else return x


    
  partial def parse_expr_logical (u: Unit): P Expr := do 
    let l <- parse_expr_compare u
    if (<- pkwd? "and") then do
        pkwd! "and"
        let r <- parse_expr u
        return Expr.expr_binop l binop_type.and r
    else if (<- pkwd? "or") then do
        pkwd! "or"
        let r <- parse_expr u
        return Expr.expr_binop l binop_type.or r
    else  return l

  partial def parse_list_commas (u: Unit) : P Expr := do
    pnote $ "parsing list with commas"
    let args <- pintercalated '[' (parse_expr u) ',' ']'
    return  (Expr.expr_list args)

  partial  def parse_list_range2 (u: Unit) : P Expr := do
    pconsume '['
    let first <- parse_expr u
    psym! ".."
    let last <- parse_expr u
    return Expr.expr_range2 first last

  partial  def parse_list_range3 (u: Unit) : P Expr := do
    pconsume '['
    let first <- parse_expr u
    psym! ","
    let snd <- parse_expr u
    psym! ".."
    let last <- parse_expr u
    return Expr.expr_range3 first snd last
  
 -- | TODO: refactor for better errors!
-- 21. ranges
-- https://www.gap-system.org/Manuals/doc/ref/chap21.html#X79596BDE7CAF8491
  partial def parse_list (u: Unit) : P Expr := do 
    pnote $ "parsing list"
    parse_list_commas u
    -- por (parse_list_commas u) $ (parse_list_range2 u)
  
  partial def parse_permutation (u: Unit): P Expr := 
        perror "don't know how to parse permutation"

  partial def parse_expr_leaf (u: Unit) : P Expr := do
    if (<- psym? "\"") then do
       let s <- pstr
       return Expr.expr_str s
    else if (<- pkwd? "true") then  do
           pkwd! "true"
           return (Expr.expr_bool true)
    else if (<- pkwd? "false") then do
           pkwd! "false"
           return (Expr.expr_bool false)
    else if (<- pkwd? "not") then do
           pkwd! "not"
           let e <- parse_expr u
           return Expr.expr_not e
    else if (<- pkwd? "function") then 
      do parse_fn_defn u
    else if (<- psym? "[") then parse_list u
    else if (<- psym? "(") then parse_permutation u
    else if (<- psym? "-") then do
             psym! "-"
             let e <- parse_expr u
             return Expr.expr_neg e
    else if (<- p2peek? pnumber) then do
      let n <- pnumber
      return Expr.expr_num n
    else if (<- pident?) then do
           let ident <- pvar!
           if (<- psym? "(") then do
             let args <- pintercalated '(' (parse_expr u) ',' ')'
             return Expr.expr_fn_call ident args
           else return Expr.expr_var ident
    else
      pnote $ "unknown leaf" 
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
         pconsume '-'
         let r <- parse_expr u
         return Expr.expr_binop l binop_type.sub r
    | some 'm' => do
           match (<- pkwd? "mod") with
              | true => do
                  let r <- parse_expr u
                  return Expr.expr_binop l binop_type.mod r
              | false => return l
    | _ => return l

-- TODO: write a higher order function that generates this.
partial def parse_expr_compare (u: Unit) : P Expr := do
  let l <- parse_arith_add_sub_mod u
  if (<- psym? "=") then do
         psym! "="
         let r <- parse_expr u
         return Expr.expr_binop l binop_type.eq r
  else if (<- psym? "<>") then do
         psym! "<>"
         let r <- parse_expr u
         return Expr.expr_binop l binop_type.neq r
  else if (<- psym? "<") then do
         psym! "<"
         let r <- parse_expr u
         return Expr.expr_binop l binop_type.lt r
  else if (<- psym? ">") then do
         psym! ">"
         let r <- parse_expr u
         return Expr.expr_binop l binop_type.gt r
  else return l
 

--  | returns true/false based on whether varargs or not
partial def parse_fn_args (u: Unit) : P (List String × Bool) := do
  psym! "("
  if (<- psym? ")")
  then do
    psym! ")"
    return ([], false)
  else do
    -- <rest_args> = ")" | "," "..." ")" | ", " <arg>  <rest_args>
    -- | TODO: consider using ppeekstar!
    let rec p_rest_args (u: Unit): P (List String × Bool) := do
          if (<- psym? ")") then do
            psym! ")"
            return ([], false)
          else do
            pconsume ','
            if (<- psym? "...") 
            then do
                psym! "..."
                psym! ")"
                return ([], true)
            else do
              let x <- pvar!
              -- | TODO: I want to ban all uses of por.
              -- let (xs, varargs?) <- por (p_rest_args u) (psuccess ([], false))
              let (xs, varargs?) <- (p_rest_args u)
              return (x::xs, varargs?)
    let x <- pvar!
    let (xs, varargs?) <- (p_rest_args u)
    return (x::xs, varargs?)
   
partial def parse_fn_locals (u: Unit) : P (List String) := do
  if (<- pkwd? "local") 
  then do
    pkwd! "local"
    let xs <- ppeekstar ',' pident!
    psym! ";"
    return xs
  else return []
    
  
partial def parse_fn_defn (u: Unit) : P Expr := do
  pnote $ "parsing function"
  pkwd! "function"
  pnote $ "parsing function args"
  let (params, varargs?) <- parse_fn_args  u
  pnote $ "parsing function locals..."
  let locals <- parse_fn_locals u
  pnote $ ". parsing statements"
  let stmts <- parse_stmts (pkwd? "end") u
  pkwd! "end"
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


 partial def p_is_fi_or_elif_or_else : P Bool := do
    if (<- pkwd? "fi") then true
    else if (<- pkwd? "elif") then true
    else if (<- pkwd? "else") then true
    else false

-- | parse the else clause of an if then else
 partial def pelse (u: Unit)  : P  ((List (Expr × List Stmt)) × Option (List Stmt)) := do
   if (<- pkwd? "elif") then do
      pkwd! "elif"
      let cond <- parse_expr u
      pkwd! "then"
      let body <- parse_stmts p_is_fi_or_elif_or_else u
      let (elifs, else_) <- pelse u
      return ((cond,body)::elifs, else_)
   else if (<- pkwd? "else") then do
          pkwd! "else"
          let stmts <- parse_stmts (pkwd? "fi") u
          pkwd! "fi"
          return ([], Option.some stmts)
    else if (<- pkwd? "fi")  then do
        pkwd! "fi"
        return ([], Option.none)
   else perror "expected elif/else/fi at end of if"


partial def parse_if (u: Unit) : P Stmt := do
  pkwd! "if"
  pnote $ "parsing if"
  let cond <- parse_expr u
  pnote $ "found if condition: |" ++ doc cond ++ "|"
  pkwd! "then"
  pnote $ "found if then. Now parsing body"
  let body <- parse_stmts p_is_fi_or_elif_or_else u
  let (elifs, else_) <- pelse u
  psym! ";"
  return Stmt.stmt_if cond body elifs else_


partial def parse_assgn_or_procedure_call (u: Unit) : P Stmt := do
   let lhs <- pident! -- TODO: this seems like a hack to mex
   if (<- psym? "(") then do
     let args <- pintercalated '(' (parse_expr u) ',' ')'
     psym! ";"
     return Stmt.stmt_procedure_call (Expr.expr_var lhs) args
   else if (<- psym? ":=") then do
     psym! ":="
     let rhs <- parse_expr u
     psym! ";"
     return Stmt.stmt_assign (Expr.expr_var lhs) rhs
   else perror "expected assignment with := or function call with (...) at toplevel"

  

partial def parse_for(u: Unit): P Stmt := do
  pkwd! "for"
  let var <- pident!
  pkwd! "in"
  let e <- parse_expr u
  pkwd! "do"
  let body <- parse_stmts (pkwd? "od") u
  psym! ";"
  return Stmt.stmt_for var e body

  partial def parse_stmt (u: Unit) : P Stmt := do
  if (<- pkwd? "if") then parse_if u
  else if (<- pkwd? "for") then parse_for u
  else if (<- pkwd? "return") then do
    pkwd! "return"
    let e <- parse_expr u
    pnote $ "found return expr |" ++ doc e ++ "|"
    psym! ";"
    return Stmt.stmt_return e
  else parse_assgn_or_procedure_call u


  -- | note to self: these give *worse* error messages!
  partial def parse_expr (u: Unit): P Expr := parse_expr_logical u

  end

partial def parse_toplevel (u: Unit): P (List Stmt) :=
  parse_stmts peof? u



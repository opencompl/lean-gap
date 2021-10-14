import GAP.P
import GAP.Doc

-- | no non-determinism for us!
-- | TODO: hide ppeek as well. Rely only on |psym?|
-- | TODO: consider hiding `por` as well? We use it now to parse lists.
open GAP.P hiding  pmany0 pmany1
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
    | binop_type.mod => "mod"
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
  | expr_in: Expr -> Expr -> Expr -- x \in y
  | expr_assign: (lhs: String) -> (rhs: Expr) -> Expr -- stbc.gi:33 return StabChainOp( G, rec( base := base ) );
  | expr_binop: Expr -> binop_type -> Expr -> Expr
  | expr_index: (arr: Expr) -> (ix: Expr) -> Expr
  | expr_list: (args: List Expr) -> Expr
  | expr_permutation: List (List Expr) -> Expr
  -- | nested functions? x(
  | expr_fn_defn: (params: List String) -> (is_vararg?: Bool) -> (locals: List String) ->
        (body: List Stmt) -> Expr
  inductive Stmt 
  | stmt_expr: (lhs: Expr) -> Stmt
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
        "[" ++ expr_to_doc a ++ ".." ++ expr_to_doc z ++ "]"
    | Expr.expr_range3 a b z =>
        "[" ++ expr_to_doc a ++ ", " ++ expr_to_doc b ++ ".." ++ expr_to_doc z ++ "]" 
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
    | Expr.expr_in l r => expr_to_doc l ++ " in " ++ expr_to_doc r
    | Expr.expr_assign lhs rhs => doc lhs ++ " := " ++ expr_to_doc rhs
    | Expr.expr_binop x op y => 
      expr_to_doc x ++ " " ++ doc op ++ " " ++ expr_to_doc y
    | Expr.expr_index arr ix => 
      expr_to_doc arr ++ "[" ++ expr_to_doc ix ++ "]"
    | Expr.expr_list args => 
      "[" ++ intercalate_doc (args.map expr_to_doc) ", " ++ "]"
    | Expr.expr_permutation cycles => 
      let doc_cycles :=  
        cycles.map (fun c => "(" ++ intercalate_doc (c.map expr_to_doc) ", " ++ ")")
      String.join doc_cycles
    | Expr.expr_fn_defn args vararg? locals body =>
      let doc_args := intercalate_doc args ", "
      let doc_vararg :=  (if vararg? then "..." else "")
      let doc_locals : Doc := 
        if locals.isEmpty then "" 
        else "local " ++ intercalate_doc locals ", " ++ ";"
    
      vgroup ["function (" ++ doc_args ++ doc_vararg ++ ")",
              nest_vgroup $ [doc_locals] ++ (body.map stmt_to_doc),
              "end"]

  partial def stmt_to_doc(s: Stmt): Doc := 
    match s with
    | Stmt.stmt_expr e => expr_to_doc e ++ ";"
    | Stmt.stmt_assign lhs rhs =>
      expr_to_doc lhs ++ " := " ++ expr_to_doc rhs ++ ";"
    | Stmt.stmt_procedure_call fn args => 
        let doc_args := intercalate_doc (args.map expr_to_doc) ", "
        expr_to_doc fn ++ "(" ++ doc_args ++ ")" ++ ";"
    | Stmt.stmt_if cond then_ elifs else_ =>
      let docs_if : List Doc := 
        ["if " ++ expr_to_doc cond ++ " then", nest_vgroup $ then_.map stmt_to_doc] 
      let docs_elifs : List Doc :=
        List.join ∘ elifs.map $
          (fun (cond, body) => 
            ["elif " ++ expr_to_doc cond ++ " then",
             nest_vgroup $ body.map stmt_to_doc]) 
      let docs_else : List Doc := 
        match else_ with 
        | some else_ => ["else", nest_vgroup $ else_.map stmt_to_doc]
        | none => []      
      vgroup $  docs_if ++ docs_elifs ++ docs_else ++ [doc "fi;"]
    | Stmt.stmt_return e => "return " ++ expr_to_doc e ++ ";"
    | Stmt.stmt_for lhs rhs body =>
        vgroup ["for " ++ lhs ++ " in " ++ expr_to_doc rhs ++ " do",
                nest_vgroup $ body.map stmt_to_doc, doc "od;"]  
end

instance : Pretty Expr where
  doc := expr_to_doc 

instance : Pretty Stmt where
  doc := stmt_to_doc 

def keywords : List String := 
  ["if", "then", "elif", "else", "fi"
   , "do", "od"
   , "for", "in"
   , "true", "false"
   , "and", "or", "not", "mod"
   , "function", "return", "end"
   , "local"
   , "in" -- hack? GAP doesn't list it as a keyword, but as some kind of parser hack.
   ]

mutual



  -- | cannot have a ppeek_symbol because one symbol can be a proper
  -- | prefix of another, so we are not sure how to tokenize!
  -- partial def ppeek_symbol: P (Option String) := perror "foo"
  
  -- | TODO: rewrite using low level API?
  partial def pkwd? (s: String): P Bool := do
   if not $ keywords.contains s then do
     pdebugfail $ "can only peek  keywords, |" ++ s ++ "| is not keyword"
   else psym? s -- TODO, HACK: this reuses symbol. 

  partial def pkwd! (s: String) : P Unit := do
   if not $ keywords.contains s then do
     pdebugfail $ "can only peek  keywords, |" ++ s ++ "| is not keyword"
   else psym! s -- TODO, HACK: this reuses symbol.
  
  partial def pvar!: P String := do
    let x <- pident!
    if keywords.contains x then do 
    perror $ "expected variable, found keyword: |" ++ x ++ "|"
    else return x


    
  -- | HACK: I don't know if this is where it really fits in!
  partial def parse_expr_in (u: Unit) : P Expr := do
    let l <- parse_expr_logical u
    if (<- pkwd? "in") then do
       pkwd! "in"
       let r <- parse_expr u
       return Expr.expr_in l r
    else return l

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
    let args <- pintercalated '[' (parse_expr u) ',' ']'
    return  (Expr.expr_list args)

  partial  def parse_list_range2 (u: Unit) : P Expr := do
    psym! "["
    let first <- parse_expr u
    psym! ".."
    let last <- parse_expr u
    psym! "]"
    return Expr.expr_range2 first last

  partial  def parse_list_range3 (u: Unit) : P Expr := do
    pconsume '['
    let first <- parse_expr u
    psym! ","
    let snd <- parse_expr u
    psym! ".."
    let last <- parse_expr u
    psym! "]"
    return Expr.expr_range3 first snd last
  
 -- | TODO: refactor for better errors!
-- 21. ranges
-- https://www.gap-system.org/Manuals/doc/ref/chap21.html#X79596BDE7CAF8491
  partial def parse_list (u: Unit) : P Expr := do 
    por (parse_list_range2 u) $ (parse_list_commas u)
  
  -- | parse the rest of the permutation given the first element.
  -- The cursor is at the first comma:
  -- (a , b , c)
  --    ^
  partial def parse_permutation_at_comma (e: Expr) (u: Unit): P Expr := do
    -- go := "," arg ")" | "," arg go   
    pnote $ "parsing permutation"

    psym! ","
    let es <- pCommasUntil1 (parse_expr u) "," ")"
    let cyc0 := e :: es -- first cycle

    let rec other_cycles (u: Unit): P (List (List Expr)) := do 
      if (<- psym? "(") then do 
        let cyc <- pintercalated '(' (parse_expr u) ',' ')' 
        let cycs <- other_cycles u
        return cyc::cycs
      else return []  
    let cycs <- other_cycles u
    return Expr.expr_permutation $ [cyc0] ++ cycs

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
    else if (<- psym? "(") then do 
      -- either (expr) or (expr, expr, expr, ...) [for permutation]
      psym! "("
      if (<- psym? ")")
      then do psym! ")"; return Expr.expr_permutation [[]] -- empty permutation
      else do 
        let e <- parse_expr u
        if (<- psym? ")")
        then do psym! ")"; return e
        else do parse_permutation_at_comma e u -- must have a comma
    else if (<- psym? "-") then do
            psym! "-"
            let e <- parse_expr u
            return Expr.expr_neg e
    else if (<- p2peek? pnumber) then do
      let n <- pnumber
      return Expr.expr_num n
    else if (<- pident?) then do
          let ident <- pvar!
          -- lambda: <ident> -> <expr>
          if (<- psym? "->") then do
            psym! "->"
            let rhs <- parse_expr u
            let vararg? := false
            let locals := []
            let body := [Stmt.stmt_return rhs]
            return Expr.expr_fn_defn [ident] vararg? locals body
          -- fn call [this is JANKY]
          else if (<- psym? "(") then do
             let args <- pintercalated '(' (parse_expr u) ',' ')'
             return Expr.expr_fn_call ident args
          -- list composition v{w} [this is JANKY]
          else if (<- psym? "{") then do 
            psym! "{"
            let f <- parse_expr u
            psym! "}"
            return Expr.expr_list_composition ident f
          -- assignment x := y [JANKY]
          else if (<- psym? ":=") then do
            psym! ":="
            let rhs <- parse_expr u
            return Expr.expr_assign ident rhs
          -- field accessor | x.y.z [JANKY]
          -- else if (<- psym? ".") then do
          --   parse_field_access ident
          else return Expr.expr_var ident
    else
      let eof <- peof?
      pnote $ "unknown leaf. EOF? |" ++ (if eof then "true" else "false" ) ++ "|" 
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
         pconsume '+'
         let r <- parse_expr u
         return Expr.expr_binop l binop_type.add r
    | some '-' => do
         pconsume '-'
         let r <- parse_expr u
         return Expr.expr_binop l binop_type.sub r
    | some 'm' => do
           if (<- pkwd? "mod")then do
                pkwd! "mod"
                let r <- parse_expr u
                return Expr.expr_binop l binop_type.mod r
            else return l
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
            if (<- psym? "...") 
            then do
                psym! "..."
                psym! ")"
                return ([], true)
            else do
              pconsume ','
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
    let xs <- pCommasUntil1 pvar! "," ";"
    return xs
  else return []
    
  
partial def parse_fn_defn (u: Unit) : P Expr := do
  pkwd! "function"
  let (params, varargs?) <- parse_fn_args  u
  let locals <- parse_fn_locals u
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
  let cond <- parse_expr u
  pkwd! "then"
  let body <- parse_stmts p_is_fi_or_elif_or_else u
  let (elifs, else_) <- pelse u
  psym! ";"
  return Stmt.stmt_if cond body elifs else_


-- partial def parse_lval (u: Unit) : P Stmt := do 
--   let var <- pident!

partial def parse_stmt_expr_or_assign_or_procedure_call (u: Unit) : P Stmt := do
  --  let lhs <- pident! -- TODO: this seems like a hack to me.
  let lhs <- parse_expr u -- TODO: this seems like a hack to me.
  -- if (<- psym? ":=") then do
  --    psym! ":="
  --    let rhs <- parse_expr u
  --    psym! ";"
  --   --  return Stmt.stmt_assign (Expr.expr_var lhs) rhs
  --    return Stmt.stmt_assign  lhs rhs
  -- else 
  match lhs with 
  | Expr.expr_fn_call fn args => do
      psym! ";"
      Stmt.stmt_procedure_call (Expr.expr_var fn) args
  | Expr.expr_assign lhs rhs => do
      psym! ";"
      Stmt.stmt_assign (Expr.expr_var lhs) rhs
  | _ => 
      psym! ";"
      Stmt.stmt_expr lhs
     -- perror $ "only top level expressions allowed are calls and assignments. Found |" ++ doc lhs ++ "|"

  

partial def parse_for(u: Unit): P Stmt := do
  pkwd! "for"
  let var <- pident!
  pkwd! "in"
  let e <- parse_expr u
  pkwd! "do"
  let body <- parse_stmts (pkwd? "od") u
  psym! "od"
  psym! ";"
  return Stmt.stmt_for var e body

  partial def parse_stmt (u: Unit) : P Stmt := do

  if (<- pkwd? "if") then parse_if u
  else if (<- pkwd? "for") then parse_for u
  else if (<- pkwd? "return") then do
    pkwd! "return"
    let e <- parse_expr u
    psym! ";"
    return Stmt.stmt_return e
  else parse_stmt_expr_or_assign_or_procedure_call u


  -- | note to self: these give *worse* error messages!
-- // expr ->
-- // expr_in[in] -> 
-- // expr_logical[and, or] ->
-- // expr_compare[>=, <=] ->
-- // expr_arith_add_sub[+, -] ->
-- // expr_arith_mul_div[*, /] -> 
-- // expr_exponential[^] ->
-- // expr_index["expr[index]"] ->
-- // expr_leaf
  partial def parse_expr (u: Unit): P Expr := parse_expr_in u

  end

partial def parse_toplevel (u: Unit): P (List Stmt) :=
  parse_stmts peof? u



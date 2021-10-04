  import GAP.P
  import GAP.Doc

  open GAP.P

  namespace GAP.AST

  inductive binop_type
  | add: binop_type
  | sub: binop_type
  | mul: binop_type
  | div: binop_type


  inductive logical_op_type
  | and: logical_op_type
  | or: logical_op_type

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


  inductive Stmt 
  | stmt_assign: (lhs: Expr) -> (rhs: Expr) -> Stmt
  | stmt_procedure_call: (name: String) -> (args: List Expr) -> Stmt
  | stmt_fn_defn: (params: List String) -> (is_vararg?: Bool) -> (locals: List String) ->
        (body: List Stmt) -> Stmt
  | stmt_if: (cond: Expr) ->
    (then_: List Stmt) -> (elifs: List (Expr × List Stmt)) -> (else_: Option Stmt) -> Stmt
  | stmt_return: (e: Expr) -> Stmt
  | stmt_for: (iter: String) -> (rhs: Expr) -> (body: List Stmt) -> Stmt
  -- TODO: add while


mutual
  partial def parse_expr_logical (u: Unit): P Expr := do 
    let l <- parse_expr u
    let mkwd <- ppeek_ident
    match mkwd with
    | _ => return l

  partial def parse_expr (u: Unit): P Expr := parse_expr_logical u
  end

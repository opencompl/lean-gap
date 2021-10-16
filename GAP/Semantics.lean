import Std.Data.AssocList
import GAP.AST
import GAP.Group
import GAP.P
open Std
open GAP.Doc
open GAP.AST
open GAP.Group
open GAP.Doc.Pretty
open GAP.P

-- TODO: consider how to write denotational?
namespace GAP.Semantics

-- 1) SMALLSTEP
-- ============


inductive Val where
| val_perm: Permutation -> Val 
| val_group: GeneratingSet -> Val -- TODO: will we have other representations of groups?
| val_bool: Bool -> Val
| val_int: Int -> Val


-- | lol, just in case we decide to implement
-- normalization by evaluation!
def val_to_expr (v: Val): Expr := sorry

instance : Pretty Val where
  doc (v: Val) := 
    match  v with
    | Val.val_perm p => toString p
    | Val.val_group gs => 
        "<" ++ "|".intercalate (RBMap.set_to_list $ RBMap.set_map gs (fun g => toString g) (compare' := compare)) ++ ">"
    | Val.val_bool b => toString b
    | Val.val_int i => doc i

  
  

instance : Inhabited Val where
  default := Val.val_int 42

def val_int? (v: Val): Result Doc Int :=
match v with
| Val.val_int i => Result.ok i
| _ => Result.err $ "expected integer, found |" ++ doc v ++ "|"


open Val
open Expr
open Stmt

-- https://math.stackexchange.com/q/1358030
-- | any odd parity element is generated by 3 cycles.
def val_An (n: Int): Val := do
  let mut gs := RBMap.empty 
  for (i: Nat) in List.range (n.toNat + 1) do 
    gs := RBMap.set_insert gs (Permutation.from_cycle [0, 1, i])
  return Val.val_group gs
  
-- | environment
abbrev Env := AssocList String Val


-- | inductive proposition modelling smallstep
inductive StepExpr: Env -> Expr -> Val -> Prop := 
| step_expr_var: (env: Env)
   -> (var: String)
   -> (val: Val)
   -> (VAL: env.find? var = Option.some val)
   -> StepExpr env (expr_var var) val
| step_expr_int: (env: Env) 
  -> (i: Int) 
  -> StepExpr env (expr_int i) (val_int i)
| step_expr_permutation: (env: Env)
   -> (vs: List Val)
   -> (es: List Expr)
   -- | TODO: need to unwrap the vals as ints etc.
   -> StepExpr env (expr_permutation p) (val_perm (Permutation.identity ))
| step_expr_call_An: (env: Env) 
  -> (n: Int) 
  -- | hacked up notion of alternating group construction
  -> StepExpr env (expr_fn_call "AlternatingGroup" [expr_int n]) (val_An n)
| step_expr_in: (env: Env) 
    -> (ep: Expr) 
    -> (egs: Expr)
    -> (p: Permutation)
    -> (gs: GeneratingSet) 
    -> (PVAL: StepExpr env ep (val_perm p))
    -> (GSVAL: StepExpr env egs (val_group gs))
    -> (member?: Bool)
    -> (MEMBER?: member? = ((generate gs).contains p))
    -> StepExpr env (expr_in ep egs)  (val_bool member?)


inductive StepStmt: Env -> Stmt -> Env -> Prop := 
| step_stmt_assign: (env: Env)
    -> (lhs: String)
    -> (rhs: Expr)
    -> (v: Val)
    -> (RHS: StepExpr env rhs v)
    -> StepStmt env (stmt_assign (expr_var lhs) rhs) (env.cons lhs v)



-- 2) EXECUTABLE
-- ============

-- Efficient reasoning about executable semantics in Coq:
-- https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.486.1300&rep=rep1&type=pdf
-- TODO: relating (1) and (2):
-- TODO: Theorem to be proved: StepExpr e v <-> execute_expr e = v

partial def execute_expr (env: Env) (e: Expr) : Result Doc Val := 
  match e with
  | expr_var var => Result.ok (env.find? var).get!
  | expr_int i => Result.ok (Val.val_int i)
  | expr_bool b => Result.ok (Val.val_bool b)
  | expr_fn_call "AlternatingGroup" [en] => do
     let n <- execute_expr env en >>= val_int?
     return val_An n
  | expr_permutation xss => do 
    let xss_ints <- xss.mapM (fun xs => 
        xs.mapM (fun e => execute_expr env e >>= val_int?))
    Result.ok (val_perm $ Permutation.from_cycles xss_ints)
  | expr_in ep egs =>
      match execute_expr env ep with
      | Result.ok (val_perm p) => 
          match execute_expr env egs with
          | Result.ok (val_group gs) => 
              return val_bool ((generate gs).contains p)
          | err => err
      | err => err
  | e => Result.err $ vgroup ["unhandled expr: ", doc e]

partial def execute_stmt (env: Env) (s: Stmt): Result Doc Env :=
match s with
| stmt_assign (expr_var lhs) rhs => do
    let vrhs <- execute_expr env rhs
    return env.cons lhs vrhs
| s => Result.err $ vgroup ["unhandled stmt:", doc s]


def init_env : Env := AssocList.empty

def assoc_list_to_list (xs: AssocList α β): List (α × β) :=
  match xs with
  | AssocList.nil => []
  | AssocList.cons k v xs => (k,v)::assoc_list_to_list xs

instance : Pretty Env where
  doc := fun env =>  
    let doc_kv : String × Val → Doc := 
      fun (k, v) => doc k ++ " := " ++ doc v
    let env_list : List (String × Val)
      := assoc_list_to_list env
    vgroup $ env_list.map doc_kv


partial def execute_stmts 
   (env: Env) (s: List Stmt) : Result Doc Env :=
  match s with
  | [] => Result.ok env
  | s::ss => do
      let env' <- execute_stmt env s
      execute_stmts env' ss

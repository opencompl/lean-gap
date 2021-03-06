-- parser combinator library
import GAP.Doc

open GAP.Doc
open Pretty
open String
open Char

namespace GAP.P
open GAP.Doc

inductive Result (e : Type) (a : Type) : Type where 
| ok: a -> Result e a
| err: e -> Result e a
| debugfail : e -> Result e a


def resultBind (ma: Result e a) (a2mb: a -> Result e b): Result e b :=
 match ma with
 | Result.ok a => a2mb a 
 | Result.err e => Result.err e -- TODO: accumulate errors?
 | Result.debugfail e => Result.debugfail e

instance : Monad (Result e) where
  pure := Result.ok
  bind := resultBind

instance [Inhabited e] : Inhabited (Result e a) where
   default := Result.err (Inhabited.default) 


inductive ErrKind : Type where
| mk : (name : String) -> ErrKind

instance : ToString ErrKind := {
  toString := fun k => 
    match k with
    | ErrKind.mk s => s
}


instance : Inhabited ErrKind where
   default := ErrKind.mk ""


structure Loc where
  line : Int
  column : Int
  ix : Int

instance : Inhabited Loc where
   default := { line := 1, column := 1, ix := 0 }

instance : Pretty Loc where
   doc (loc: Loc) := doc loc.line ++ doc ":" ++ doc loc.column


def locbegin : Loc := { line := 1, column := 1, ix := 0 }

 
def advance1 (l: Loc) (c: Char): Loc :=
  if c == '\n'
    then { line := l.line + 1, column := 1, ix := l.ix + 1  }
    else return { line := l.line, column := l.column + 1, ix := l.ix + 1}

-- | move a loc by a string.
partial def advance (l: Loc) (s: String): Loc :=
  if isEmpty s then l
  else let c := s.front; advance (advance1 l c) (s.drop 1)


structure Note where
  left : Loc
  right : Loc
  kind : Doc


instance : Inhabited Note where
   default := 
     { left := Inhabited.default 
       , right := Inhabited.default
       , kind := Inhabited.default }

instance : Pretty Note where 
  doc (note: Note) := 
      doc note.left ++ " " ++  note.kind


-- | TODO: enable notes, refactor type into Loc x String x [Note] x (Result ParseError a)
structure P (a: Type) where 
   runP: Loc -> List Note -> String ->  (Loc × (List Note) × String × (Result Note a))



-- | map for parsers
def pmap (f : a -> b) (pa: P a): P b := {
  runP :=  λ loc ns s => 
    match pa.runP loc ns s with
      | (l, ns, s, Result.ok a) => (l, ns,  s, Result.ok (f a))
      | (l, ns, s, Result.err e) => (l, ns, s, Result.err e)
      | (l, ns, s, Result.debugfail e) => (l, ns, s, Result.debugfail e)
}


-- https://github.com/leanprover/lean4/blob/d0996fb9450dc37230adea9d10ecfdf10330ef67/tests/playground/flat_parser.lean
def ppure {a: Type} (v: a): P a := { runP :=  λ loc ns s =>  (loc, ns, s, Result.ok v) }

def pbind {a b: Type} (pa: P a) (a2pb : a -> P b): P b := 
   { runP := λloc ns s => match pa.runP loc ns s with 
            | (l, ns, s, Result.ok a) => (a2pb a).runP l ns  s
            | (l, ns, s, Result.err e) => (l, ns, s, Result.err e)
            | (l, ns, s, Result.debugfail e) => (l, ns, s, Result.debugfail e)
   }

instance : Monad P := {
  pure := ppure,
  bind := pbind
}

-- | eat till '\n'
partial def eat_line_ (l: Loc) (s: String): Loc × String :=
  if isEmpty s then (l, s)
  else let c := front s
  if c == '\n'
  then (l, s)
  else return eat_line_ (advance1 l c) (s.drop 1)

partial def eat_whitespace_ (l: Loc) (s: String) : Loc × String :=
    if isEmpty s
    then (l, s)
    else  
     let c:= front s
     -- if isPrefixOf "//" s
     if c == '#'
     then 
      let (l, s) := eat_line_ l s
      eat_whitespace_ l s
     else if c == ' ' || c == '\t'  || c == '\n'
       then eat_whitespace_ (advance1 l c) (s.drop 1)
       else (l, s)



def pnote [Pretty α] (a: α): P Unit := {
  runP := λ loc ns s => 
   let (loc, s) := eat_whitespace_ loc s
    let n := { left := loc, right := loc, kind := doc a }
    (loc, ns ++ [n], s, Result.ok ())
}

def perror [Pretty e] (err: e) :  P a := {
  runP := λ loc ns s =>
  let (loc, s) := eat_whitespace_ loc s
  (loc, ns, s, Result.err ({ left := loc, right := loc, kind := doc err}))
}

def pdebugfail [Pretty e] (err: e) :  P a := {
  runP := λ loc ns s =>
    let (loc, s) := eat_whitespace_ loc s
    (loc, ns, s, Result.debugfail ({ left := loc, right := loc, kind := doc err}))
}


instance : Inhabited (P a) where
   default := perror "INHABITED INSTANCE OF PARSER"

def psuccess (v: a): P a := { 
    runP := λ loc ns s  => 
      (loc, ns, s, Result.ok v)
  }


-- | run p. if it accepts, return the result. 
-- | if it fails, then return none
def pmay (p: P a): P (Option a) := { 
    runP := λ loc ns s  => 
      match p.runP loc ns s with
        |  (loc, ns, s, Result.ok v) => (loc, ns, s, Result.ok (Option.some v))
        | (loc, ns, s, Result.err e) => (loc, ns, s, Result.ok Option.none)
        | (l, ns, s, Result.debugfail e) => (l, ns, s, Result.debugfail e)
  }

-- | run p. if it accepts, then retun te *old* state with true.
-- if it fails, then return the *old* state with false.
-- effectively converts any p into its peeking version.
def p2peek? (p: P a): P Bool := { 
    runP := λ loc ns s  => 
      match p.runP loc ns s with
        |  (loc', ns', s', Result.ok v) => (loc, ns, s, Result.ok true)
        | (loc', ns', s', Result.err e) => (loc, ns, s, Result.ok false)
        | (loc', ns', s', Result.debugfail e) => (loc', ns', s', Result.debugfail e)
  }



-- try p. if success, return value. if not, run q
-- TODO: think about what to do about notes from p in por.
def por (p: P a) (q: P a) : P a :=  {
  runP := λ loc ns s => 
    match p.runP loc ns s with
      | (loc', ns', s', Result.ok a) => (loc', ns', s', Result.ok a)
      | (loc', ns', s', Result.err e) => q.runP loc ns s
      | (l, ns, s, Result.debugfail e) => (l, ns, s, Result.debugfail e)
}

-- def pors (ps: List (p a)) : P a := 
--  match ps with
--  | [] => []
--  | [p] => p
--  | (p::ps) por p (pors ps)



-- | never fails.
def ppeek : P (Option Char) := { 
  runP := λ loc ns haystack =>
    if isEmpty haystack
    then (loc, ns, haystack, Result.ok none)
    else do
     let (loc, haystack) := eat_whitespace_ loc haystack
     (loc, ns, haystack, Result.ok ∘ some ∘ front $ haystack)
  }

-- | return true if EOF
def peof? : P Bool := {
  runP := λ loc ns haystack => 
     let (loc, haystack) := eat_whitespace_ loc haystack
    (loc, ns, haystack, Result.ok (isEmpty haystack))
}

partial def psym? (sym: String): P Bool :=  {
  runP := λ loc notes s => 
     let (loc, s) := eat_whitespace_ loc s
     return (loc, notes, s, Result.ok (isPrefixOf sym s))
}

private def padvance_str_INTERNAL (s: String) : P Unit := {
  runP := λ loc ns scur => (advance loc s, ns, drop scur (length s), Result.ok ())
}


partial def psym! (s: String): P Unit := do
  match (<- psym? s) with
  | true => 
     padvance_str_INTERNAL s
     psuccess ()
  | false => perror $ "expected symbol |" ++ s ++ "|"


private def padvance_char_INTERNAL (c: Char) : P Unit := {
  runP := λ loc ns haystack => (advance1 loc c, ns, drop haystack 1, Result.ok ())
}

def pconsume(c: Char) : P Unit := do
  let cm <- ppeek
  match cm with 
  | some c' => 
     if c == c' then padvance_char_INTERNAL c
     else perror ("pconsume: expected character |" ++ toString c ++ "|. Found |" ++ toString c' ++ "|.")
  | none =>  perror ("pconsume: expected character |" ++ toString c ++ "|. Found EOF")


def ppeek?(c: Char) : P Bool := do
  let cm <- ppeek
  return (cm == some c)

partial def peekwhile (predicate: Char -> Bool)
   (s: String)
   (out: String): String :=
      if isEmpty s 
      then ""
      else 
        let c := front s;
        if predicate c
        then peekwhile predicate (s.drop 1) (out.push c)
        else out

-- | never fails, returns empty string till it can read something that
-- | matches predicate
partial def ppeekwhile (predicate: Char -> Bool): P String := {
  runP := λ loc ns s => (loc, ns, s, Result.ok (peekwhile predicate s ""))
}

def eat_whitespace : P Unit := {
  runP := λ loc ns s =>
    let (l', s') := eat_whitespace_ loc s
    (l', ns, s', Result.ok ())
  }


partial def takeWhile (predicate: Char -> Bool)
   (startloc: Loc)
   (loc: Loc)
   (s: String)
   (out: String):  (Loc × String × Result Note String) :=
      if isEmpty s 
      then (loc, s, Result.err {left := startloc, 
                                right := loc,
                                kind := "expected delimiter but ran out of string"})
      else 
        let c := front s;
        if predicate c
        then takeWhile predicate startloc (advance1 loc c) (s.drop 1) (out.push c)
        else (loc, s, Result.ok out)

partial def ptakewhile (predicateWhile: Char -> Bool) : P String :=
{ runP := λ startloc ns haystack => 
      let (loc, s) := takeWhile predicateWhile startloc startloc haystack ""
      (loc, ns, s)
}



-- | take an identifier. TODO: ban symbols
def pident! : P String := do
   eat_whitespace
   let mc <- ppeek
   match mc with
  | Option.none => perror $ "expected identifier, found EOF"
  | Option.some c => 
         let s <- ppeekwhile (fun c => c.isAlphanum || c == '_')
         match s.toNat? with 
         | some nat => perror $ "expected identifier, found number |" ++ toString nat ++ "|"
         | none => psuccess () 
         padvance_str_INTERNAL s
         return s

partial def pident?: P Bool := p2peek? pident!    
 

def pnumber : P Int := do
  eat_whitespace
  match (<- ppeek) with
  | some leading =>
    if not leading.isDigit
    then perror $ "expected number, found |" ++ doc leading ++ "|"
    else 
      -- | take till whitespace, then convert to number
      -- this is to ensure that things like '2n' [which are legal identifiers in gap!]
      -- are considered identifiers, not numbers.
      let name <- ptakewhile (fun c => c.isAlphanum || c == '_')
      match name.toInt? with
      | some num => return num
      | none => perror $ "expected number, found |" ++ name ++ "|."
  | none => perror $ "expected number, found EOF"
  
-- | pCommasUntil1 p comma until is <a> [<until> | <comma> <pCommasUntil1>] 
-- <p> <comma> follwed by pCommasUntil. This also consumes the until.

partial def pCommasUntil1 (p: P a) (comma: String) (until: String) : P (List a) := do
  let a <- p
  if (<- psym? comma) then do
    psym! comma
    let as <- pCommasUntil1 p comma until 
    return a::as
  else if (<- psym? until) then do
    psym! until
    return [a]
  else perror $ "expected |" ++ comma ++ "| or |" ++ until ++ "|."

-- parse an [ <r> | <i> <p> <pintercalated_> ]
partial def pintercalated_ (p: P a) (i: Char) (r: Char) : P (List a) := do
  eat_whitespace
  match (<- ppeek) with
   | some c => -- perror ("intercalate: I see |" ++ c.toString ++ "|")
               if c == r
               then do pconsume r; return []
               else if c == i
               then do
                 pconsume i
                 eat_whitespace
                 let a <- p
                 let as <- pintercalated_ p i r
                 return (a :: as)
               else perror ("intercalate: expected |" ++ doc i ++ "|  or |" ++ doc r ++ "|, found |" ++ c.toString ++ "|.")
   | _ =>  perror ("intecalate: expected |" ++ doc i ++ "|  or |" ++ doc r ++ "|, found EOF" )


-- | parse things starting with a <l>, followed by <p> intercalated by <i>, ending with <r>
partial def pintercalated [Pretty a] (l: Char) (p: P a) (i: Char) (r: Char) : P (List a) := do
  eat_whitespace
  pconsume l
  match (<- ppeek) with
   | some c => if c == r
               then do pconsume r; return []
               else do
                  let a <- p
                  let as <- pintercalated_ p i r 
                  return (a :: as)
   | _ => perror "expected either ')' or a term to be parsed. Found EOF"


partial def pstr : P String :=  do
   eat_whitespace
   pconsume '"'
   let s <- ptakewhile (fun c => c != '"')
   pconsume '"'
   return s


-- | ppeekstar peeks for `l`.
-- | (a) If it finds `l`, it returns `p` followed by `ppeekstar l`.
-- |(ii) If it does not find `l`, it retrns []
partial def ppeekstar (l: Char) (p: P a) : P (List a) := do
  let proceed <- ppeek? l
  if proceed then do 
        let a <- p
        let as <- ppeekstar l p
        return (a :: as)
  else return []


partial def pmany0 [Pretty a]  (p: P a) : P (List a) := do
  match (<- pmay p) with
    | Option.some a => do
        pnote $ "pmany0: found " ++ doc a
        let as <- pmany0 p
        return (a::as)
    | Option.none =>
        pnote $ "pmany0: found none"
       return []

-- | parse <p>+ for a given <p>
partial def  pmany1 [Pretty a] (p: P a) : P (List a) := do
  let a1 <- p
  let as <- pmany0 p
  return (a1::as)



-- | find minimum k such that 
-- s[pos + k*dir] == '\n'
partial def find_newline_in_dir
   (s: String)
   (pos: Int)
   (dir: Int): Int :=
 if pos <= 0
 then 0
 else if pos >= s.length - 1 then Int.ofNat (s.length - 1)
 else if s.get pos.toNat == '\n' then pos - dir
 else find_newline_in_dir s (pos + dir) dir


-- | find rightmost newline in s[0, pos].
partial def find_earlier_newline
   (s: String)
   (pos: Int): Int := find_newline_in_dir s pos (-1)

-- | find leftmost newline in s[pos, end]
partial def find_later_newline
   (s: String)
   (pos: Int): Int := find_newline_in_dir s pos 1


-- | add a pointer showing file contents at the line where `note` lies.
def note_add_file_content (contents: String) (note: Note): Doc :=
  let ixl := find_earlier_newline contents note.left.ix
  let ixr := find_later_newline contents note.right.ix
  -- | closed interval
  let len := ixr - ixl + 1
  let substr : Substring := (contents.toSubstring.drop ixl.toNat).take len.toNat
  let nspaces : Int := note.left.ix - ixl
  let underline : String :=   ("".pushn ' ' nspaces.toNat).push '^'
  vgroup [doc "---|" ++ note.kind ++ "|---" 
          , doc note.left ++ " " ++ substr.toString
          , doc note.left ++ " " ++ underline
          , doc "---"]

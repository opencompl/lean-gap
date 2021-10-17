import Std.Data.RBMap
import Std.Data.AssocList
import Lean.CoreM -- tests/lean/run/trace.lean
import GAP.QuickCheck

open Lean
open Std

-- https://github.com/leanprover/lean4/blob/master/src/Std/Data/AssocList.lean#L10

namespace GAP.Group

open Std


instance [ToString α ] [ToString β] {compare: α -> α -> Ordering}: ToString (RBMap α β compare) where
  toString (x: RBMap α β compare) := 
    toString (x.toList)

instance [BEq α ] [BEq β] {compare: α -> α -> Ordering}: BEq (RBMap α β compare) where
  beq (x y: RBMap α β compare) := 
    BEq.beq (x.toList) (y.toList) -- TODO: this assumes they are made into lists based on ordering!


abbrev Set (α : Type) (compare: α -> α -> Ordering) := RBMap α Unit compare


inductive Permutation where 
| mk: RBMap Int Int (compare) -> Permutation

instance : ToString Permutation where
  toString (p: Permutation) := 
    match p with
    | Permutation.mk p =>  p.toList.toString
instance {α: Type} {β: Type} {compare: α -> α -> Ordering} : Inhabited (RBMap α β compare) where
  default := RBMap.empty

instance : Inhabited Permutation where 
  default := Permutation.mk RBMap.empty


def compareTuple [Ord α] [Ord β] (p: α × β) (q: α × β)  : Ordering := 
            match compare p.fst q.fst with
            | Ordering.lt => Ordering.lt
            | Ordering.gt => Ordering.gt
            | Ordering.eq => compare p.snd q.snd 

instance [Ord α] [Ord β] : Ord (α × β) where
    compare := compareTuple


def Permutation.from_cycle (cyc: List Int) : Permutation :=
  -- | map cyc[0] -> cyc[1], cyc[1] -> cyc[2], ...
  let adj_maps : List (Int × Int) := cyc.zip (cyc.drop 1)
  match cyc.getLast? with
  | Option.some last => 
   -- map last -> head, rest
    Permutation.mk $ RBMap.fromList ((last, cyc.head!)::adj_maps) compare
  | Option.none => Permutation.mk $ RBMap.empty -- permutation is empty

def Permutation.act(p: Permutation) (a: Int): Int :=
  match p with
  | Permutation.mk p => 
    match p.find? a with
    | some b => b
    | none => a

def Permutation.largest_moved (p: Permutation): Int := 
match p with
| Permutation.mk xs => xs.fold  (fun out x y => max x (max y out)) 0

partial def permutation_lex_order (p: Permutation) (q: Permutation) : Ordering := 
    let n := max p.largest_moved q.largest_moved
    let rec go (i: Int): Ordering := 
        if i > n then Ordering.eq
        else 
            match compare (p.act i) (q.act i) with
            | Ordering.lt => Ordering.lt
            | Ordering.gt => Ordering.gt
            | Ordering.eq => go (i + 1)
    go 0

instance : Ord Permutation where
    compare := permutation_lex_order


-- | create range [0..n]
partial def range_le_n (n: Int): List Int := 
  -- go i has list [0..i)
  let rec go (i: Int) (acc: List Int) : List Int :=
    if i > n then acc
    else go (i + 1) (i::acc)
  go 0 []

instance : BEq Permutation where
   beq p q := 
      let n := max p.largest_moved q.largest_moved
      (range_le_n n).all $ fun i => p.act i == q.act i


def Permutation.identity : Permutation := Permutation.mk RBMap.empty

-- act (mul p q) x = act p (act q x)
def mul (p: Permutation) (q: Permutation) : Permutation :=
  let n := max p.largest_moved q.largest_moved
  let xs := range_le_n n
  Permutation.mk $ RBMap.fromList (xs.map fun x => (x, p.act (q.act x))) compare

def inverse (p: Permutation): Permutation := 
match p with
| Permutation.mk p => 
  Permutation.mk $ RBMap.fromList (p.toList.map (fun (x, y) => (y, x))) compare

def Permutation.from_cycles (cycs: List (List Int)): Permutation :=
  let accum (p: Permutation) (cyc: List Int):= 
    mul p (Permutation.from_cycle cyc) 
  cycs.foldl accum Permutation.identity 

partial def orbit (p: Permutation) (x: Int): Set Int compare := 
  let rec go (p: Permutation) (start: Int) (cur: Int) : Set Int compare :=
      if start == cur then RBMap.empty
      else 
        let rest := go p start (p.act cur)
        RBMap.insert rest cur ()
  let rest := go p x (p.act x)
  RBMap.insert rest x () 


def RBMap.union_set {α: Type} {compare:α -> α -> Ordering} (xs: Set α compare) (ys: Set α compare): Set α compare := 
  RBMap.fromList (xs.toList ++ ys.toList) compare

partial def cycles_rec (p: Permutation) (kmax: Int) (k: Int)  (seen: Set Int compare): List (Set Int compare) :=
if k == kmax then []
else 
  if seen.contains k then cycles_rec p kmax k seen
    else
    let orb := orbit p k
    let seen := RBMap.union_set orb seen
    if orb.size <= 1 then (cycles_rec p kmax (k+1) seen)
    else orb :: (cycles_rec p kmax (k+1) seen)

def cycles (p: Permutation): List (Set Int compare) := 
    cycles_rec p (p.largest_moved) 0 (RBMap.empty)

def cycle_to_string (cyc: Set Int compare) : String := 
  "(" ++ " ".intercalate (cyc.toList.map toString) ++ ")"

def permutation_to_string (p: Permutation) : String := 
  String.join $ (cycles p).map cycle_to_string


-- | map a child number to the parent node, and the permutation that goes
-- from the child to the parent. child -> (σ, parent) such that act σ child = parent
abbrev SchrierVector := AssocList Int (Option (Permutation × Int))
      

partial def least_nonfixed_rec (p: Permutation) (i: Int) :=
  if p.act i != i then i else least_nonfixed_rec p (i + 1)

def least_nonfixed (p: Permutation) : Int := least_nonfixed_rec p 0


abbrev GeneratingSet := Set Permutation compare

def sims_filter (g: GeneratingSet) (sn: Int) : GeneratingSet := sorry


def RBMap.set_bind {α: Type} {compare: α -> α -> Ordering} (xs: Set α compare) (f: α -> Set α compare): Set α compare :=
  RBMap.fold (fun new a () => RBMap.union_set new (f a)) RBMap.empty xs 

def RBMap.set_map {α: Type} {compare: α -> α -> Ordering} (xs: Set α compare) (f: α -> β) {compare': β -> β -> Ordering}: Set β compare' := 
    RBMap.fold (fun new a () => RBMap.insert new (f a) ()) RBMap.empty xs

def RBMap.set_subtract {α: Type} {compare: α -> α -> Ordering} (all: Set α compare) (to_remove: Set α compare): Set α compare :=
  RBMap.fold (fun all' a () => RBMap.erase all' a) to_remove all 

def RBMap.set_singleton {α: Type} (a: α) (compare: α -> α -> Ordering): Set α compare :=
    RBMap.fromList [(a, ())] compare

def RBMap.set_empty {α: Type} (compare: α -> α -> Ordering): Set α compare :=
    RBMap.empty

def RBMap.set_from_list {α: Type} (as: List α) (compare: α -> α -> Ordering): Set α compare :=
    RBMap.fromList (as.map (fun a => (a, ()))) compare

def RBMap.set_insert {α: Type} {compare: α -> α -> Ordering} (as: Set α compare) (a: α): Set α compare :=
    RBMap.insert as a ()

def RBMap.set_union {α: Type} {compare: α -> α -> Ordering} (s1 s2: Set α compare): Set α compare := 
   s1.fold (fun out k () => RBMap.set_insert out k) s2

partial def randSetM (minSize: Nat) (maxSize: Nat) (ra: Rand α)  {compare: α -> α -> Ordering}:
    Rand (Set α compare) := do 
   let size <- randIntM minSize maxSize
   let rec go (s: Set α compare) := 
    if s.size == size
    then return s
    else do 
        let a <- ra
        go (RBMap.set_insert s a) 
    go (RBMap.set_empty compare)

-- 
def RBMap.union_keep_right {α: Type} {compare: α -> α -> Ordering}
    (s1 s2: RBMap α  β compare): RBMap α  β compare := 
   s1.fold (fun out k v => out.insert k v) s2

def RBMap.set_to_list {α: Type} {compare: α -> α -> Ordering} (as: Set α compare): List α := 
    (RBMap.toList as).map (fun (a, ()) => a)

-- filter seems expensive?
def RBMap.set_filter {α: Type} (p: α → Bool)
    {compare: α -> α -> Ordering} (as: Set α compare): Set α compare := do
    let mut out := RBMap.set_empty compare
    for (a, ()) in as do
        if p a then
        out := RBMap.insert out a ()
    return out

-- | generate all permutations from the generating set
partial def generate_rec (gs: GeneratingSet) (out: Set Permutation compare): Set Permutation compare := do
  let mut next := out
  let mut changed : Bool := False
  for (h, ()) in out do
     for (g, ()) in gs do
       let gh := mul g h
       if RBMap.contains next gh
       then continue
       else do
          changed := True 
          next := RBMap.set_insert next gh
  if changed
  then generate_rec gs next
  else next


-- | this is too slow, implement better version..
def generate (gs: GeneratingSet) : Set Permutation compare := 
  generate_rec gs (RBMap.set_singleton Permutation.identity compare)

def fst (x: α × β) : α :=  match x with | (a, _) => a
def snd (x: α × β) : β :=  match x with | (_, b) => b

-- | map element in the orbit to the element that created it.
partial def generating_set_orbit_rec (gs: GeneratingSet) 
    (frontier: RBMap Int Permutation compare)
    (out: RBMap Int Permutation compare): RBMap Int Permutation compare := do

    let mut frontier' : RBMap Int Permutation compare := RBMap.empty -- new frontier set.
    let mut out' := out -- new out set

    for (i, p) in frontier do
        for (g, ()) in gs do -- TODO: create ADT set.
            let (i', p') := (g.act i, mul g p)
            if out'.contains i'
            then continue -- skip already seen elements
            else
               out' := out'.insert i' p' 
               frontier' := frontier'.insert i' p'  

    if frontier'.isEmpty
    then out'
    else generating_set_orbit_rec gs frontier' out'

-- | compute the orbit of an element under a generating set
def GeneratingSet.orbit (gs: GeneratingSet) (k: Int): RBMap Int Permutation compare :=
  let frontier := RBMap.fromList [(k, Permutation.identity)] compare
  generating_set_orbit_rec gs frontier frontier


--  we have a group G = <gs>
--  We have k ∈ S, and we need to find hs ⊂ G such that <hs> = Stab(k).
--  We have partitioned G into cosets of Stab(k) via (o[0] Stab(k), ..., o[n] Stab(k)).
--    These are called os[:] since they are Cosets of the Stabilizer,
--    which are in bijection with *O*rbits. [Orbit stabilizer]
--  Key idea: we have a sort of "splitting"
--    find coset             return coset repr.
--  G ----------> G/Stab(k) -------------------> G
--  Call the composite map defect: G -> G, since it measures how far an element is from
--  living in Stab(k). See that defect(h) = e iff h ∈ Stab(k).
-- 
--  Now consider: remove_defect (h: G) : G := defect(h).inverse() * h
--  `remove_defect` 'inverts' the defect. It allows `h` to act, sending k to some element of Orb(k).
--   it then undoes the defect [by defect(h).inverse()], moving it back to `k`. So we have
--   k --h----------> l ∈Orb(k) --defect(h).inverse()---> k
--   k --defect(h)--> l ∈Orb(k) --defect(h).inverse()---> k
-- 
--  Thus, for all g ∈ G, we have remove_defect(g) ∈ Stab(k).
-- 
--  It is now plausible that: <gs> = G => < gs.map(remove_defect) > = Stab(k)
--  since  remove_defect forces elements to stabilize k,
--  and we apply this treatment to all of G(by modifying the generator). 
--  
--  However, the weird part is that THAT's NOT ENOUGH.
--  Rather, we need the generators to be: < (gs * os).map(remove_defect) >
--  For whatever reason, we must take all pairs of gs, os!
def GeneratingSet.stabilizer_subgroup_generators 
 (gs: GeneratingSet) (k: Int) : GeneratingSet :=  do
    -- | treat these as representatives of stabilizer cosets.
    let orbit : RBMap Int Permutation compare := gs.orbit k
    let purify (g: Permutation) : Permutation :=
        let orep := (orbit.find! (g.act k))
        mul  (inverse orep) g -- remove the part of `g` that causes it to move `k` to `o`.

    let mut out : GeneratingSet := RBMap.set_empty compare -- TODO: make compare implicit arg
    for (g, ()) in gs do
        for (_, p) in orbit do 
            out := RBMap.set_insert out (purify (mul g p))
    return out


-- | cmputes stab gs [0..k] :: schrier_decomposition_rec gs (k+1)
partial def schrier_decomposition_rec 
  (gs:  GeneratingSet) (k: Int): List (GeneratingSet) := 
   if gs == RBMap.set_singleton Permutation.identity compare
   then [gs]
   else 
     let stab : GeneratingSet := gs.stabilizer_subgroup_generators k
     stab :: schrier_decomposition_rec stab (k+1)

-- | produces schrier decomposition, where first element is
-- | G = Stab([0..-1])
-- second element is subgrop of G which is stab([0..0]), and so on.
-- last element is {e} = Stab[0..n].
def schrier_decomposition(gs:  GeneratingSet) : List (GeneratingSet) := 
    schrier_decomposition_rec gs (-1)

def schrier_order (gs: GeneratingSet): Int := do 
    let sch := schrier_decomposition gs
    let mut size := 1
    let mut ix := -1 -- we stabilize [0..ix]
    for stab_le_ix in sch do
        -- | we stabilize [0..ix], so we should find size of orbit of (ix + 1), smallest
        -- thing we do move.
        size := size * (GeneratingSet.orbit stab_le_ix (ix + 1)).size
        ix := ix + 1
    return size

-- | generate a random permutation of [1..n] with fisher yates 
partial def rand_permutation (n: Int): Rand Permutation := do
   let rec go (i: Int) (unseen: List Int): Rand (List (Int × Int)) := do
    if unseen.isEmpty then return []
    else
       let r <- randOneOf unseen
       let unseen := List.filter (fun v => v != r) unseen
       let rest <- go (i+1) unseen
       return (i, r)::rest
   let xs := range_le_n n
   let shuffled <- go 0 xs
   return Permutation.mk (RBMap.fromList shuffled compare) 

def test_permutation_group_inverse: IO (TestResult Unit) :=
    testRandom "p * inv p == id"  (rand_permutation 5) $ fun (p: Permutation) => do
    --   p =?= inverse p
      (mul p (inverse p)) =?= Permutation.identity

def test_permutation_group_assoc: IO (TestResult Unit) :=
    let gen := rand3 (rand_permutation 5) (rand_permutation 5) (rand_permutation 5)
    testRandom "(p * (q * r)) == ((p * q) * r)" gen $
      fun ((p, q, r): Permutation × Permutation × Permutation) => do
        -- let (p, q, r) := pqr
        mul p (mul q r) =?= mul (mul p q) r


def test_permutation_group_id: IO (TestResult Unit) := do
    let _ <- testRandom "p * id == p" (rand_permutation 5) $ fun (p: Permutation) => 
      (mul p Permutation.identity) =?= p
    testRandom "id  * p == p" (rand_permutation 5) $ fun (p: Permutation) =>
      (mul Permutation.identity p) =?= p


-- | return true if these two maps share a (k, v) pair
def RBMap.set_intersects?
    {compare: α -> α -> Ordering}
    (as: Set α compare) (as': Set α compare) : Bool := do
    for (k, ()) in as do
        match RBMap.find? as' k with
        | some () => return True
        | none => continue
    return false

def RBMap.set_intersect
    {compare: α -> α -> Ordering}
    (as: Set α compare) (as': Set α compare) : Set α compare := do
    let mut out : Set α compare := RBMap.set_empty compare
    for (k, ()) in as do
        match RBMap.find? as' k with
        | some () => out := RBMap.set_insert out k
        | none => continue
    return out


-- | test that orbit 
def test_orbit: IO (TestResult Unit) := 
    testRandom (ntests := 10) "orbit" 
      (rand2 (randSetM 1 5 $ rand_permutation 5) (randIntM 1 5)) fun ((ps, k): Set Permutation compare × Int) => do
    let orb_and_perms : RBMap Int Permutation compare := GeneratingSet.orbit ps k 

    for (i, p) in orb_and_perms do
         p.act k =?= i
    return ()


-- | test that we compute orbit permutation elements correctly by checking that 
-- | their cosets are indeed cosets (ie, disjoint)
def test_stabilizer_coset_reps_slow: IO (TestResult Unit) := 
    testRandom (ntests := 100) "stabilizer coset representatives" 
      (rand2 (randSetM 1 5 $ rand_permutation 5) (randIntM 1 5)) fun ((ps, k): Set Permutation compare × Int) => do
    let H := generate ps
    let Stab : Set Permutation compare := 
        RBMap.set_filter (fun h => h.act k == k) H -- exhaustively create stabilizer

    let orb_and_perms : RBMap Int Permutation compare := 
         GeneratingSet.orbit ps k 

    -- | map each element k' in the orbit [k--p-->k'] to its coset representatve pH
    -- v slow to map? slow to build?
    let mut orb_and_cosets : RBMap Int (Set Permutation compare) compare := RBMap.empty
    for (i, p) in orb_and_perms do 
        orb_and_cosets := orb_and_cosets.insert i (RBMap.set_map H (fun h => mul p h))

    let mut result : TestResult Unit := TestResult.success ()
    for (i, p) in orb_and_perms do
        for(j, q) in orb_and_perms do
            if j <= i  then continue
            let i_coset : Set Permutation compare := RBMap.set_map Stab (fun s => mul p s)
            let j_coset : Set Permutation compare := RBMap.set_map Stab (fun s => mul q s)
            if RBMap.set_intersects? i_coset j_coset
            then 
                result := TestResult.failure $ 
                    "stabilizer coset intersection " ++ toString p ++ ", " ++ toString q
                break
        if result.failure? then break
    result


-- | test that we compute the generators of the stabilizer correctly
def test_generators_of_stabilizer: IO (TestResult Unit) :=
  testRandom (ntests := 10) "generators of stabilizer" 
      (rand2 (randSetM 1 5 $ rand_permutation 5) (randIntM 1 5)) fun ((ps, k): Set Permutation compare  × Int) => do
        -- | TODO: write rand_set
        let G := generate ps
        let stab_exhaustive := RBMap.set_filter (fun g => g.act k == k) G 
        let stab_generated := generate (GeneratingSet.stabilizer_subgroup_generators ps k)
        -- | TODO: add toString for Set
        stab_exhaustive =?= stab_generated

def test_schrier_order: IO (TestResult Unit) :=
  testRandom (ntests := 10) "test order computation using schrier decomposition" 
      ((randSetM 1 5 $ rand_permutation 5)) fun (ps: Set Permutation compare) => do
        -- | TODO: write rand_set
        let G := generate ps
        let order_exhaustive := (generate ps).size
        let order_fast := schrier_order ps
        Int.ofNat order_exhaustive =?= order_fast

-- | actually I need monad transformer
def tests: IO (TestResult Unit) := do
  let _ <- test_permutation_group_inverse
  let _ <- test_permutation_group_assoc
  let _ <- test_orbit
  let _ <- test_stabilizer_coset_reps_slow
  let _ <- test_generators_of_stabilizer
  let _ <- test_schrier_order
  test_permutation_group_id

-- | todd coxeter
def toddCoxeter : IO Unit := return ()

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

    let mut frontier' : RBMap Int Permutation compare := RBMap.empty
    let mut out' := out

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
    else generating_set_orbit_rec gs frontier out'

-- | compute the orbit of an element under a generating set
def GeneratingSet.orbit (gs: GeneratingSet) (k: Int): RBMap Int Permutation compare :=
  let frontier := RBMap.fromList [(k, Permutation.identity)] compare
  generating_set_orbit_rec gs frontier (RBMap.empty)
  -- frontier


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
        mul g (inverse orep) -- remove the part of `g` that causes it to move `k` to `o`.

    let mut out : GeneratingSet := RBMap.set_empty compare -- TODO: make compare implicit arg
    for (g, ()) in gs do
        for (_, p) in orbit do 
            let gp := mul g p
            out := RBMap.set_insert out (purify gp)
    return out

partial def schrier_decomposition_rec 
  (gs:  GeneratingSet) (k: Int): List (GeneratingSet) := 
   if gs == RBMap.set_singleton Permutation.identity compare
   then [gs]
   else 
     let stab : GeneratingSet := gs.stabilizer_subgroup_generators  k
     gs :: schrier_decomposition_rec stab (k+1)


def schrier_decomposition(gs:  GeneratingSet) : List (GeneratingSet) := 
    schrier_decomposition_rec gs 0



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


def intersects? {α: Type} [BEq α]  (as: List α) (as': List α) := 
 match as with
 | [] => false
 | a::as => if as'.contains a then true else intersects? as as'

-- | test that orbit 
def test_orbit: IO (TestResult Unit) := 
    testRandom (ntests := 10) "orbit" 
      (rand2 (randSetM 1 5 $ rand_permutation 5) (randIntM 1 5)) fun ((ps, k): Set Permutation compare × Int) => do
    let orb_and_perms : RBMap Int Permutation compare := GeneratingSet.orbit ps k 

    for (i, p) in orb_and_perms do
         p.act k =?= i
    return ()
    
    -- -- | check that union of all cosets is the full H
    -- let union_cosets : Set Permutation compare := 
    --     orb_and_cosets.fold (fun out o h => RBMap.set_union out h) (RBMap.set_empty compare)
    -- union_cosets =?= H



-- | test that we compute orbit permutation elements correctly by checking that 
-- | their cosets are indeed cosets
def test_stabilizer_coset_reps_slow: IO (TestResult Unit) := 
    testRandom (ntests := 10) "stabilizer coset representatives" 
      (rand2 (randListM 1 5 $ rand_permutation 5) (randIntM 1 5)) fun ((ps, k): List Permutation × Int) => do
    let H := generate (RBMap.set_from_list ps compare) -- exhaustive generate group
 
    let Stab := RBMap.set_filter (fun h => h.act k == k) H -- exhaustively create stabilizer

    let orb_and_perms : RBMap Int Permutation compare := 
         GeneratingSet.orbit (RBMap.set_from_list ps compare) k 

    -- | map each element k' in the orbit [k--p-->k'] to its coset representatve pH
    -- v slow to map? slow to build?
    let mut orb_and_cosets : RBMap Int (Set Permutation compare) compare := RBMap.empty
    for (i, p) in orb_and_perms do 
        orb_and_cosets := orb_and_cosets.insert i (RBMap.set_map H (fun h => mul p h))

    let mut result : TestResult Unit := TestResult.success ()
    for (i, Stabi) in orb_and_cosets do
        for(j, Stabj) in orb_and_cosets do
            if j <= i  then continue
            if intersects? (RBMap.toList Stabi) (RBMap.toList Stabj) then
                result := TestResult.failure $ "cosets must have empty intersection"
                break
        if result.failure? then break

    if result.failure? then result
    
    
    -- -- | check that union of all cosets is the full H
    -- let union_cosets : Set Permutation compare := 
    --     orb_and_cosets.fold (fun out o h => RBMap.set_union out h) (RBMap.set_empty compare)
    -- union_cosets =?= H


-- | test that we compute the generators of the stabilizer correctly
def test_generators_of_stabilizer: IO (TestResult Unit) :=
  testRandom (ntests := 10) "generators of stabilizer" 
      (rand2 (randListM 1 5 $ rand_permutation 5) (randIntM 1 5)) fun ((ps, k): List Permutation × Int) => do
        -- | TODO: write rand_set
        let ps := RBMap.set_from_list ps compare
        let G := generate ps
        let stab_exhaustive := RBMap.set_filter (fun g => g.act k == k) G 
        let stab_generated := generate (GeneratingSet.stabilizer_subgroup_generators ps k)
        -- | TODO: add toString for Set
        stab_exhaustive =?= stab_generated


-- | actually I need monad transformer
def tests: IO (TestResult Unit) := do
  let _ <- test_permutation_group_inverse
  let _ <- test_permutation_group_assoc
  let _ <- test_orbit
  let _ <- test_stabilizer_coset_reps_slow
  -- let _ <- test_generators_of_stabilizer
  test_permutation_group_id



/-
class Permutation:
    def __init__(self, mapping: Dict[int, int]):
        assert Permutation.find_non_bijection_witness(mapping) is None
        self.mapping = self.remove_redundancies_in_mapping(mapping)

    def __hash__(self):
        return hash(tuple(list(self.mapping.items())))

    def __eq__(self, other):
        nmax = max(self.sn(), other.sn())
        for i in range(nmax):
            if self(i) != other(i): return False
        return True


    @classmethod
    def from_cycles(cls, cycles):
        assert isinstance(cycles, list)
        mapping = {}
        for cyc in cycles:
            assert isinstance(cyc, list)
            l = len(cyc)
            for i in range(len(cyc)):
                mapping[cyc[i]] = cyc[(i+1)%l]
        return Permutation(mapping)

    # sort by lex ordering.
    def __lt__(self, other):
        nmax = max(self.sn(), other.sn())
        for i in range(nmax):
            if self(i) == other(i): continue
            if self(i) < other(i): return True
            if self(i) > other(i): return False
        return False

    @classmethod
    def remove_redundancies_in_mapping(self, mapping):
        out = {}
        for x in mapping:
            if mapping[x] == x:
                continue
            out[x] = mapping[x]
        return out

    @classmethod
    def find_non_bijection_witness(self, mapping):
        # if bijetion, return none. otherwise return x1, x2 in mapping such that mapping[x1] == mapping[x2]
        # check injective, surjective is by definition
        inverse_images = {}
        for (x, y) in mapping.items():
            if y in inverse_images:
                return x, inverse_images[y]
            else:
                inverse_images[y] = x
        return None

    def sn(self): # find largest number in domain/codomain
        n = 0
        for(x, y) in self.mapping.items():
            n = max(n, x, y)
        return n

    def __call__(self, i):
        if i in self.mapping:
            return self.mapping[i]
        return i

    @classmethod
    def identity(self):
        return Permutation({})

    def inverse(self):
        inverse = {}
        for (x, y) in self.mapping.items():
            inverse[y] = x
        return Permutation(inverse)


    # (g.compose_left_of(h))(x) = g(h(x))
    def compose_left_of(g, h):
        domain = set()
        domain = domain.union(h.mapping.keys())
        domain = domain.union(g.mapping.keys())

        mapping = { x : g(h(x)) for x in domain}
        return Permutation(mapping)


    def __eq__(self, other):
        N = max(self.sn(), other.sn())
        for i in range(N):
            if self(i) != other(i): return False
        return True

    # (g * h)(x) = g(h(x))
    def __mul__(self, other): 
        return self.compose_left_of(other)

    def is_identity(self):
        for k in self.mapping:
            if self.mapping[k] != k: return False
        return True

    def __repr__(self):
        cycs = self.cycles()
        return f"Permutation({cycs})"

    __str__ = __repr__

    def cycles(self) -> Set[List[int]]:
        cycles = []
        seen = set()
        for x in range(self.sn()):
            if x in seen: continue
            xpow = x
            cycle = []
            while xpow not in seen:
                cycle.append(xpow)
                seen.add(xpow)
                xpow = self(xpow)
            if len(cycle) > 1:
                cycles.append(cycle)
        return cycles



# def make_permutation_group(n: int) -> set(Permutation):
#     if n == 0: return { Permutation({ 0 : 0 }) }
# 
#     ps = make_permutation_group(n-1)
# 
#     # have 0..n position the n value can be sent to.
#     for i in range(n+1):

# Rubick's cube perspective: https://www.jaapsch.net/puzzles/schreier.htm


# https://math.stackexchange.com/questions/1662723/can-someone-explain-how-the-schreier-sims-algorithms-works-on-a-permutation-grou

# https://mathstrek.blog/2018/06/12/schreier-sims-algorithm/
# A: subset of Sn
# G := <A>: subgroup generated by A
# Sn acts on [n] := { 1...n }

# pick a random element k ∈ [n], consider its orbit under G. We know that Size(O[k]) = Size(G|) / Size(Stab[k])
# start by setting O[k] := {k}, expand by allowing elements of A to act on O[k]
# If we can can recursively find Size(Stab[k]), we are done [or so it seems? Stab[k] lives in 2^G, not 2^[n] ]
# We need representatives for left cosets of G.


# compute how to reach [1..n] rom k ∈ [n] using as
# maps a number `c` to the permutation that links its parent `p` to `c`. So we have:
# schrier_vector[c].inverse()[c] = p
# This gives us the orbit. For if an element k ∈ n is not reachable, it will be listed as None.
def schrier_vector(as_: List[Permutation], k: int, n:int) -> List[Permutation]:
    assert k < n
    vs = [None for _ in range(n)]
    vs[k] = Permutation.identity()
    changed = True
    while changed:
        changed = False
        for i in range(n):
            if vs[i] is None: continue
            for a in as_:
                if vs[a(i)] is None: changed = True; vs[a(i)] = a
                ainv = a.inverse()
                if vs[ainv(i)] is None: changed = True; vs[ainv(i)] = ainv
    return vs



# Find smallest index i such that p(i) != i.
# That is, for all small < i, p(small) = small, and p(i) != i
def least_nonfixed(p: Permutation, n:int) -> int:
    assert not p.is_identity()
    for i in range(n):
        # loop invariant: ∀ small < i, p(small) = small)
        if p(i) == i: continue
        # can't have p(i) < i because we are dealing with permutations, and for all
        # indeces small < i, we have pinv(small) = small, since p(small) = small is loop invariant.
        assert p(i) > i 
        return (i, p(i))
    raise RuntimeError("didn't find non-fixed value though not identity")

# return as_ to size n(n-1)/2;
def sims_filter(as_: List[Permutation], n:int):
    table = [[None for j in range(n)] for i in range(n)]

    for a in as_:
        while not a.is_identity():
            (i, j) = least_nonfixed(a, n)
            if table[i][j] is None:
                table[i][j] = a
                break
            else:
                # should this not be a = a * table[i][j].inverse()
                a = a.inverse() * table[i][j] # strikes me as weird.
                # see that anew(i) = i, since
                # - aprev(i) = j ; aprev_inv(j) = i
                # - table[i][j](i) = j
                # - thus (aprev_inv * table[i][j])(i) = aprev_inv(j) = i
                # so we have that least_nonfixed(anew) > least_nonfixed(a)
    s = set()
    for i in range(n):
        for j in range(i+1, n):
            if table[i][j] is None: continue
            s.add(table[i][j])
    return s


# given generators, generate the full group
def generate_from_generators(ps: List[Permutation]):
    H = set(); H.add(Permutation.identity())
    while True:
        Hnew = set()
        for h in H:
            for p in ps:
                hnew = h * p
                if hnew in H: continue
                Hnew.add(hnew);

        if not Hnew: return H
        else: H = H.union(Hnew)
    return H


# returns a map of elements in the orbit of k to the permutation that sends them there.
# see that there are coset representatives by the orbit stabilizer theorem.
def stabilizer_coset_representatives_slow(gs: Set[Permutation], k: int, n:int) -> Dict[int, Permutation]:
    gs = set(gs)
    gs.add(Permutation.identity())
    orb2rep = {}
    orb2rep = { k : Permutation.identity() }

    while True:
        new_orb2rep = {}
        # terrible, O(n^2). use some kind of tree search!
        for g in gs:
            # rep es coset representative for orb ∈ Orbit(k)
            for (orb, rep) in orb2rep.items(): 
                repnew = g * rep; orbnew = repnew(k)
                if orbnew in orb2rep: continue # have already seen
                new_orb2rep[orbnew] = repnew
        # no update
        if not new_orb2rep: return orb2rep
        orb2rep.update(new_orb2rep)


# we have a group G = <gs>
# We have k ∈ S, and we need to find hs ⊂ G such that <hs> = Stab(k).
# We have partitioned G into cosets of Stab(k) via (o[0] Stab(k), ..., o[n] Stab(k)).
#   These are called os[:] since they are Cosets of the Stabilizer,
#   which are in bijection with *O*rbits. [Orbit stabilizer]
# Key idea: we have a sort of "splitting"
#   find coset             return coset repr.
# G ----------> G/Stab(k) -------------------> G
# Call the composite map defect: G -> G, since it measures how far an element is from
# living in Stab(k). See that defect(h) = e iff h ∈ Stab(k).

# Now consider: remove_defect (h: G) : G := defect(h).inverse() * h
# `remove_defect` 'inverts' the defect. It allows `h` to act, sending k to some element of Orb(k).
#  it then undoes the defect [by defect(h).inverse()], moving it back to `k`. So we have
#  k --h----------> l ∈Orb(k) --defect(h).inverse()---> k
#  k --defect(h)--> l ∈Orb(k) --defect(h).inverse()---> k
#
# Thus, for all g ∈ G, we have remove_defect(g) ∈ Stab(k).
#
# It is now plausible that: <gs> = G => < gs.map(remove_defect) > = Stab(k)
# since  remove_defect forces elements to stabilize k,
# and we apply this treatment to all of G(by modifying the generator). 
# 
# However, the weird part is that THAT's NOT ENOUGH.
# Rather, we need the generators to be: < (gs * os).map(remove_defect) >
# For whatever reason, we must take all pairs of gs, os!
def generators_of_stabilizer(gs: List[Permutation], k: int, n: int):
    purified = set()

    # Create coset representatives
    orb2rep = stabilizer_coset_representatives_slow(gs, k, n)

    candidates = [g * rep for g in gs for rep in orb2rep.values()]


    for h in candidates:
            o = h(k) # find where h sends k | o ∈ Orb(k)
            orep = orb2rep[o] # find coset representative corresponding to o
            # orep is hdefect, since it tells us which coset h lies in.
            # h = orep * h_k_stab
            # h_k_stab := h * orep.inverse()
            h_k_stab = orep.inverse() * h
            purified.add(h_k_stab)
    return purified



@composite
def permutations(draw, n: int):
    # raw random
    # Fishes Yates: https://en.wikipedia.org/wiki/Fisher%E2%80%93Yates_shuffle
    xs = { i : i for i in range(n) }

    i = n-1 # from (n-1), down to zero.
    while i >= 0:
        j = draw(integers(0, i)) # j ∈ [0, i]
        temp = xs[i]; xs[i] = xs[j]; xs[j] = temp; # swap
        i -= 1
    return Permutation(xs)


@given(p=permutations(n=5))
def test_permutation_group_inverse(p: Permutation):
    assert (p * p.inverse()).is_identity()
    assert (p.inverse() * p).is_identity()

@given(p=permutations(n=5), q=permutations(n=5), r=permutations(n=5))
def test_permutation_group_assoc(p: Permutation, q: Permutation, r: Permutation):
    assert (p * (q * r)) == ((p * q) * r)

@given(p=permutations(n=5))
def test_permutation_group_id(p: Permutation):
    assert (p * p.identity()) == p
    assert p == p * p.identity()


@given(ps=lists(permutations(n=5), min_size=1, max_size=4), k=integers(0, 4))
def test_schrier_vector(ps: List[Permutation], k:int):
    N = 5
    vs = schrier_vector(ps, k=k, n=N)
    assert len(vs) == N

    for x in range(N):
        # element is reachable from `k`. backtract to reach `k`.
        if vs[x]:
            y = x
            nsteps = 0
            while y != k:
                y = vs[y].inverse()(y) # NOTE: the fact that we need to invert this is SO FUGLY.
                nsteps += 1
                assert nsteps <= N  + 1
        else:
            # element is unreachable from `k`
            for p in ps:
                assert p(k) != x

    assert vs[k].identity()

@given(p=permutations(n=5))
def test_permutation_cycle_create_decompose(p: Permutation):
    assert p == Permutation.from_cycles(p.cycles())



@given(ps=lists(permutations(n=5), min_size=1, max_size=4), k=integers(0, 4))
def test_stabilizer_coset_reps_slow(ps: List[Permutation], k:int):
    N = 5
    H = generate_from_generators(ps) # exhaustive generate group
    Stab = set([h for h in H if h(k) == k]) # exhaustively create stabilizer
    orb2rep = stabilizer_coset_representatives_slow(ps, k, N)

    rep2coset = {}
    for rep in orb2rep.values():
        rep2coset[rep] = set([rep * s for s in Stab]) # create coset

    for rep1, coset1 in rep2coset.items():
        for rep2, coset2 in rep2coset.items():
            if rep1 == rep2: continue
            assert(len(coset1.intersection(coset2)) == 0) # cosets have no intersection

    union_of_cosets = set()
    for rep, coset in rep2coset.items():
        union_of_cosets.update(coset)


    assert H == union_of_cosets # check that group is equal to union of cosets of stabilizer.

@given(ps=lists(permutations(n=5), min_size=1, max_size=4), k=integers(0, 4))
def test_generators_of_stabilizer(ps: Gene, k:int):
    N = 5

    H = generate_from_generators(ps) # exhaustive generate group
    Stab = set([h for h in H if h(k) == k]) # exhaustively create stabilizer


    stab_gens = generators_of_stabilizer(ps, k, N)
    stab_generated = generate_from_generators(stab_gens)

    assert Stab == stab_generated



def factorial(n: int):
    if n == 0: return 1
    return n * factorial(n-1)

def generators_for_sn(n: int):
    if n == 0: return [Permutation.identity()]
    else: 
        n_cycle = Permutation.from_cycles([list(range(n+1))])
        swap = Permutation.from_cycles([[0,1]])
        return [swap, n_cycle]

@given(n=integers(0, 4))
def test_generators_for_sn(n: int):
    G = set(generate_from_generators(generators_for_sn(n)))
    assert len(G) == factorial(n+1) # [0..n]

# compute the schrier decomposition of <as_> = A inside Sn
def schrier_decomposition(gs: List[Permutation], n: int, use_sims_filter:bool = True) -> Dict[int, Permutation]:
    Ggens = {-1: gs} # Gss[i]: List[int] = generators of G[i]. so G[0] = < gs > = < Ggens[0] > and so on.

    gs_prev = gs
    # Ggens[k] is a subgroup of <gs> which stabilizes [0..k] pointwise
    #   [so h(0) = 0, h(1) = 1, ... h(k) = k]
    for k in range(n+1): # [0, n]
        gs_new = generators_of_stabilizer(gs_prev, k, n)
        if use_sims_filter: gs_new = sims_filter(gs_new, n) # performance
        Ggens[k] = gs_new
        gs_prev = gs_new
    return Ggens

# take many generators and make the set small
@given(gs=sets(permutations(n=5), min_size=30, max_size=50))
def test_sims_filter(gs: List[Permutation]):
    N = 5
    hs = sims_filter(gs, 5)
    assert len(hs) <= len(gs)
    assert len(hs) <= (N * (N - 1))//2
    assert generate_from_generators(gs) == generate_from_generators(hs)

@given(gs=sets(permutations(n=5), min_size=1, max_size=7))
def test_schrier_decmposition(gs: List[Permutation]):
    N = 6

    schrier = schrier_decomposition(gs, N)
    G = set(generate_from_generators(gs))

    for K in range(N+1):
        # compute stabilizer of [0..K] brute force
        stab_brute = deepcopy(G)
         # filter out everything in stab_brute that does not stabilize i ∈ [0, K]
        for i in range(0, K+1): 
            stab_brute = set(filter(lambda g: g(i) == i, stab_brute))

        # check that this is equal to the result as told by schrier
        assert stab_brute == generate_from_generators(schrier[K])
        assert len(schrier[K]) <= (N * (N - 1)) // 2 # by sims filter.


def compute_order(gs: List[Permutation], n: int):
    schrier = schrier_decomposition(gs, n)
    # let's compute |schrier[i]|/|schrier[i+1]|.
    # Recall that schrier[i] ~= Stab(schrier[i-1], i)
    # Recall that schrier[i+1] ~= Stab(schrier[i], i+1)
    # Recall that |schrier[i+1]|/|Stab(schrier[i], i+1)| ~= Orb(schrier[i+1],i+1) 
    total_size = 1
    for i in range(-1, len(schrier)):
        if i == n-1: break
        hs = schrier[i]
        # intuition: G0 has G1=Stab(G0, 1). Size of |G0|/|Stab(G0, 1)| ~= Orb(G0, 1).
        # so Gi should act on (i+1)
        vs = schrier_vector(hs, k=i+1, n=n)
        orb_size = sum([1 for v in vs if v is not None])
        print(f"orb size of {hs} is {orb_size}")
        total_size *= orb_size
    return total_size

@given(gs=sets(permutations(n=5), min_size=1, max_size=7))
def test_order(gs: Set[Permutation]):
    N = 5
    order_fast = compute_order(gs, N)
    order_brute = len(generate_from_generators(gs))
    assert order_fast == order_brute


def main():
    pass

if __name__ == "__main__":
    main()
-/

-- | todd coxeter
def toddCoxeter : IO Unit := return ()

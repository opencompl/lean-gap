import Std.Data.RBMap
import Std.Data.AssocList
import Lean.CoreM -- tests/lean/run/trace.lean
import GAP.QuickCheck

open Lean

open Std

-- https://github.com/leanprover/lean4/blob/master/src/Std/Data/AssocList.lean#L10

namespace GAP.Group

abbrev Cycle := List Int
abbrev Cycles := List Cycle
inductive Permutation where 
| mk: List (Int × Int) -> Permutation

def Permutation.support: Permutation -> List (Int × Int)
| Permutation.mk xs => xs


instance : Inhabited Permutation where 
  default := Permutation.mk []

instance : ToString Permutation where
  toString 
  | Permutation.mk xs => "(" ++ toString xs ++ ")"

instance : Shrinkable Permutation where
  shrink (p: Permutation) :=
  match p with
  | Permutation.mk xs => (Shrinkable.shrink xs).map  Permutation.mk

abbrev Set α (ord: α -> α -> Ordering) := RBMap α Unit ord



-- class SetLike (s: Type -> Type) where
--    setEmpty:  s a 
--    setSingleton: a -> s a
--    setUnion: s a -> s a -> s a
--    setDifference: s a -> s a -> s a
--    setIntersection: s a -> s a -> s a
--    
-- 
-- class MapLike (m: Type -> Type -> Type) where
--    mapEmpty:  m k v
--    mapInsert: k -> v -> m k v -> m k v
--    mapDelete: k -> m k v -> m k v
--    mapLookup: k -> m k v -> Option v
   

-- | action of permutation on element
def act_ (p: List (Int × Int)) (a: Int) : Int :=
  match p with
  | [] => a
  | (x,y)::ps => if x == a then y else act_ ps a


def Permutation.act(p: Permutation) (a: Int): Int := act_ p.support a

def permutation_largest_moved_(p: List (Int × Int)) : Int := 
match p with
| [] => 0
| (x,y)::ps => 
    let best' := permutation_largest_moved_ ps
    max x (max y best')

def Permutation.largest_moved (p: Permutation): Int := 
  permutation_largest_moved_ p.support


-- | create range [1..n]
-- | TODO: move to [1..n], currently at [0..n]!
partial def range1n (n: Int): List Int := 
  let rec go (i: Int) : List Int :=
    if i == n then [n]
    else i::go (i + 1)
  go 0

instance : BEq Permutation where
   beq p q := 
      let n := max p.largest_moved q.largest_moved
      (range1n n).all $ fun n => p.act n == q.act n

def Permutation.identity : Permutation := Permutation.mk []

def domain (p: Permutation) : List Int := p.support.map (fun (x, y) => x)

-- act (mul p q) $  x = act p $ act q x
def mul (p: Permutation) (q: Permutation) : Permutation :=
  let n := max p.largest_moved q.largest_moved
  let xs := range1n n
  Permutation.mk $ xs.map (fun x => (x, p.act (q.act x)))

def inverse (p: Permutation): Permutation := 
  Permutation.mk $ p.support.map (fun (x, y) => (y, x))

partial def orbit (p: Permutation) (x: Int): Cycle := 
  let rec go (p: Permutation) (start: Int) (cur: Int) :=
      if cur == start then [] else cur :: go p start (p.act cur)
  x :: go p x (p.act x)

-- | compute cycle decomposiition for p, given that we are currently trying to 
-- build cycle at (head cur_domain), are yet to process (rest cur_domain)
-- and have seen stuff in `seen`.
-- TODO: consider filtering cur_domain by seen?
def cycles_ (p: Permutation) (cur_domain: List Int) (seen: List Int): Cycles :=
match cur_domain with
| [] => []
| d::ds => 
    if  seen.elem d then cycles_ p ds seen
    else let orb := orbit p d
         if orb.length == 1 then (cycles_ p ds (seen ++ orb))
         else orb :: (cycles_ p ds (seen ++ orb))


def cycles (p: Permutation): Cycles := cycles_ p [] []

def cycle_to_string (c: Cycle) : String := 
  "(" ++ " ".intercalate (c.map toString) ++ ")"

def permutation_to_string (p: Permutation) : String := 
  String.join $ (cycles p).map cycle_to_string


-- | map a child number to the parent node, and the permutation that goes
-- from the child to the parent. child -> (σ, parent) such that act σ child = parent
abbrev SchrierVector := AssocList Int (Option (Permutation × Int))
      

partial def least_nonfixed_rec (p: Permutation) (i: Int) :=
  if p.act i != i then i else least_nonfixed_rec p (i + 1)

def least_nonfixed (p: Permutation) : Int := least_nonfixed_rec p 0


abbrev GeneratingSet := List Permutation

def sims_filter (g: GeneratingSet) (sn: Int) : GeneratingSet := sorry


-- | generate all permutations from the generating set
partial def generate_rec (gs: GeneratingSet) (cur: List Permutation): List Permutation := 
  let next := gs.bind (fun g => cur.map (mul g))
  let delta := next.removeAll cur
  if List.length delta  == 0
  then cur
  else generate_rec gs (cur ++ delta)

def generate (gs: GeneratingSet) : List Permutation := 
  generate_rec gs [Permutation.identity]


def fst (x: α × β) : α :=  match x with | (a, _) => a
def snd (x: α × β) : β :=  match x with | (_, b) => b

-- | map element in the orbit to the element that created it.
partial def generating_set_orbit_rec(gs: GeneratingSet) 
   (frontier: List (Int × Permutation))
   (out: List (Int × Permutation)): List (Int × Permutation)  :=
  -- | expand the BFS frontier
  let frontier: List (Int × Permutation) := 
    gs.bind (fun g => frontier.map (fun (k, h) => (g.act k, mul g h)))
  let seen : List Int := out.map fst
  -- | keep those that have not been sen
  let frontier : List (Int × Permutation) := frontier.filter (fun (k, g) => not $ seen.contains k) 
  if frontier.isEmpty
  then out
  else generating_set_orbit_rec gs frontier (out ++ frontier)



-- | compute the orbit of an element under a generating set
def GeneratingSet.orbit(gs: GeneratingSet) (k: Int): List (Int × Permutation) :=
  generating_set_orbit_rec gs [(k, Permutation.identity)] [(k, Permutation.identity)]


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
def GeneratingSet.stabilizer_subgroup_generators (gs: GeneratingSet) (k: Int) : GeneratingSet := 
  -- | treat these as representatives of stabilizer cosets.
  let orbit : List (Int × Permutation) := gs.orbit k
  let purify (o: Int) (g: Permutation) : Permutation :=
       let orep := (orbit.lookup o).get!
       mul g (inverse orep) -- remove the part of `g` that causes it to move `k` to `o`.
  -- | augment gs with information of where in the orbit it lies
  let gs : List (Int × Permutation) := gs.map (fun g => (g.act k, g))
  -- | take all products of generators (gs) with coset representatives (orbit)
  -- this effectively gives us the full group G, since we have translated the group (gs) along the orbits (o)
  let genset : List (Int × Permutation) := 
     gs.bind (fun (_, g) => orbit.map fun (o, h)  => (g.act o, mul g h))
  -- | purify
  let out := genset.map (fun (o, g) => purify o g)
  -- | remove duplicates here?
  List.eraseDups out


partial def schrier_decomposition_rec 
  (gs:  GeneratingSet) (k: Int): List (GeneratingSet) := 
   if gs == [Permutation.identity]
   then [gs]
   else 
     let stab : GeneratingSet := gs.stabilizer_subgroup_generators  k
     gs :: schrier_decomposition_rec stab (k+1)
  

def schrier_decomposition(gs:  GeneratingSet) : List (GeneratingSet) := 
  schrier_decomposition_rec gs 0



-- | generate a random permutation of [1..n] with fisher yates 

partial def rand_permutation (n: Int): Rand Permutation := 
   let rec go (i: Int) (unseen: List Int): Rand (List (Int × Int)) := do
     if i == n + 1 then return []
     else do
       let r <- randOneOf unseen
       let unseen := List.filter (fun v => v != r) unseen
       let rest <- go (i+1) unseen
        return (i, r)::rest
   let xs := range1n n
   Permutation.mk <$> go 0 xs


def test_permutation_group_inverse: IO (TestResult Unit) :=
    testRandom "p * inv p == id"  (rand_permutation 5) $ fun (p: Permutation) => do
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


-- | test that we compute orbit permutation elements correctly by checking that 
-- | their cosets are indeed cosets
def test_stabilizer_coset_reps_slow: IO (TestResult Unit) := 
    testRandom (ntests := 10) "stabilizer coset representatives" 
      (rand2 (randListM 1 5 $ rand_permutation 5) (randIntM 1 5)) fun ((ps, k): List Permutation × Int) => do
    let H := generate ps -- exhaustive generate group
    let Stab := H.filter (fun h => h.act k == k) -- exhaustively create stabilizer
    -- -- v find orbit permutations
    let orb_and_perms : List (Int × Permutation) := GeneratingSet.orbit ps k 

    -- -- -- | map each element k' in the orbit [k--p-->k'] to its coset representatve pH
    -- v slow to map? slow to build?
    let orb_and_cosets : List (Int × List (Permutation)) := 
        orb_and_perms.map $ fun (o, p) => (o, H.map (fun h => mul p h))

    let l := orb_and_cosets.length-1

    -- | return from a for loop?
    [0:l].forM $ fun i => 
      [i+1:10].forM $ fun j => 
      --   -- | cosets should have no intersection!
         let Hi := (orb_and_cosets.get! i).snd
         let Hj := (orb_and_cosets.get! j).snd
         if intersects? Hi Hj
         then TestResult.failure "cosets must have empty intersection"
         else TestResult.success ()

    -- | check that union of all cosets is the fulll H
    let union_cosets : List Permutation := orb_and_cosets.foldl (fun out (o, h) => out ++ h) $ []
    union_cosets =?= H

-- | test that we compute the generators of the stabilizer correctly
def test_generators_of_stabilizer: IO (TestResult Unit) :=
  testRandom (ntests := 10) "generators of stabilizer" 
      (rand2 (randListM 1 5 $ rand_permutation 5) (randIntM 1 5)) fun ((ps, k): GeneratingSet × Int) => do
        let G := generate ps
        let stab_exhaustive := G.filter fun g => g.act k == k
        let stab_generated := generate (ps.stabilizer_subgroup_generators k)

        stab_exhaustive =?= stab_generated


-- | actually I need monad transformer
def tests: IO (TestResult Unit) := do
  let _ <- test_permutation_group_inverse
  let _ <- test_permutation_group_assoc
  let _ <- test_stabilizer_coset_reps_slow
  let _ <- test_generators_of_stabilizer
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

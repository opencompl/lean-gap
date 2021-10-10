import Init.Data.UInt
-- import Init.Data.UInt.Bitwise

open Std

-- splitmix: http://gee.cs.oswego.edu/dl/papers/oopsla14.pdf
-- splitmix in C++: https://gist.github.com/imneme/6179748664e88ef3c34860f44309fc71
-- splitmix in haskell: https://hackage.haskell.org/package/splitmix-0.1.0.3/docs/src/System.Random.SplitMix.html#mix64

structure SplitMixState where
  seed : UInt64
  gamma : UInt64
  
def split (s: SplitMixState) : (SplitMixState × SplitMixState) := 
   (s, s)

def shiftXor (n: UInt64) (w: UInt64): UInt64 :=  w.xor (w.shiftRight n)
def shiftXorMultiply (n: UInt64) (k: UInt64) (w: UInt64) := (shiftXor n w).mul k



-- Note: in JDK implementations the mix64 and mix64variant13
-- (which is inlined into mixGamma) are swapped.
def mix64 (z0: UInt64) : UInt64 :=
   -- MurmurHash3Mixer
    let z1 := shiftXorMultiply 33 0xff51afd7ed558ccd z0
    let z2 := shiftXorMultiply 33 0xc4ceb9fe1a85ec53 z1
    let z3 := shiftXor 33 z2
    z3


def rand (s: SplitMixState) : (UInt64 × SplitMixState) := 
  (mix64 s.seed, { seed := s.seed+1, gamma := s.gamma })

partial def popcount(i: UInt64) : UInt64 := 
  let unsetMSB : UInt64 := i.land (i - 1)
  if i == 0 then 0 else 1 + popcount unsetMSB


-- http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.47.1361&rep=rep1&type=pdf
-- Delta deubgging: https://www.st.cs.uni-saarland.de/papers/tse2002/tse2002.pdf


abbrev Generator (a: Type) := Int -> a -- Int is sseed


def generatorPure (a: α): Generator α := fun i => a
def generatorBind (ma: Generator α) (a2mb: α -> Generator β): Generator β := 
  fun i =>  -- need to split
     let (j1, j2) := (i, i)
     let a : α := ma j1
     let mb : Generator β := a2mb a 
     let b : β := mb j2
     b

instance : Monad Generator where
  pure := generatorPure
  bind := generatorBind

def genTuple (ga: Generator α)  (gb: Generator β)  : Generator (α × β) := 
  fun i => (ga i, gb i) -- bad, always correlated!
  
inductive TestResult
| success
| failure



-- | return some () on success.
def testRandom [ToString α] (gen: Generator α) (predicate: α -> TestResult): IO TestResult := do
   let total := 120
   let rec go (n: Nat) : IO TestResult := 
     match n with
     | 0 => return TestResult.success
     | Nat.succ n' => do 
           let a := gen n
           match predicate (gen n) with
           | TestResult.success => do
                 IO.eprint $ "\rsucceeded test [" ++ toString (total - n + 1) ++ "/" ++ toString total ++ "]"
                 go n' 
           | TestResult.failure => do
              IO.eprintln $ "failed at counter-example(seed= " ++ toString n ++ "): " ++ toString a
              return TestResult.failure

   IO.eprintln "\n---"
   IO.eprint $ "running tests... [0/" ++ toString total ++ "]"
   let out <- go total
   match out with
   | TestResult.success => IO.eprintln "\nPassed all tests"
   | TestResult.failure => IO.eprintln "\nFailed test"
   return out

def testExhaustive (gen: Generator a) (predicate: a -> OptionM Unit) (depth: Int): IO Bool := do
   return true


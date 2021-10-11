import Init.Data.UInt
import Init.Data.Random 
-- import Init.Data.UInt.Bitwise

open Std

  
inductive TestResult
| success
| failure (err: String)

abbrev Rand α := StdGen -> α × StdGen
abbrev RandIO α := StdGen -> IO (α × StdGen)



def runRand (seed: Nat) (r: Rand α): α × StdGen :=  
  r (mkStdGen  seed)

def liftRand2RandIO (ma: Rand α): RandIO α := 
  fun gen => return (ma gen)

def liftIO2RandIO (ma: IO α): RandIO α := 
  fun gen => do
     let a <- ma
     return (a, gen)

def randPure (a: α) : Rand α := fun gen => (a, gen)
def randBind (ma: Rand α) (a2mb: α -> Rand β) : Rand β := 
      fun gen => 
        let (agen, bgen) := stdSplit gen
        let (a, gen) := ma agen
        let mb := a2mb a
        mb bgen

instance : Monad Rand where
  pure  := randPure
  bind := randBind


        

def randIOPure (a: α) : RandIO α := fun gen => return (a, gen)
def randIOBind (ma: RandIO α) (a2mb: α -> RandIO β) : RandIO β := 
      fun gen => do
        let (agen, bgen) := stdSplit gen
        let (a, gen) <- ma agen
        let mb := a2mb a
        mb bgen

instance : Monad RandIO where
  pure  := randIOPure
  bind := randIOBind

def rand2 (ra: Rand α) (rb: Rand β) : Rand (α × β) := do
  let a <- ra
  let b <- rb
  return (a, b)

def rand3 (ra: Rand α) (rb: Rand β) (rc: Rand γ) : Rand (α × β × γ) := do
  let a <- ra
  let b <- rb
  let c <- rc
  return (a, b, c)

        
def randNatM (lo: Nat) (hi: Nat) : Rand Nat := 
  fun gen => randNat gen lo hi 

-- | randomly choose one of
def randOneOf [Inhabited α] (xs: List α): Rand α := do
  let maxIx := xs.length - 1
  let randIx <- randNatM 0 maxIx
  return xs.get! randIx


def testEq [ToString α] [BEq α] (a a': α): TestResult :=
  if a == a'
  then TestResult.success
  else TestResult.failure $ toString a ++ " != " ++ toString a'

notation x "=?=" y => testEq x y

class Shrinkable (α : Type) where
  shrink: α → List α

-- | default, enables no shrinking!
instance  (priority := low): Shrinkable (α : Type) where
  shrink _ := []


instance [Shrinkable α] : Shrinkable (List α) where
  shrink (xs: List α) : List (List α) := 
    match xs with
    | [] => []
    | _ => 
       let shrinkIth {β : Type} [Shrinkable β] (bs: List β) (i: Nat) : List β :=
         let ls := (bs.take i)
         let rs := (bs.drop i)
         ls ++ rs.drop 1
         -- match rs with
         --   | [] => [ls]
         --   | r::rs => 
         --        let rsmalls := (Shrinkable.shrink r)
         --        match rsmalls with 
         --        | [] => [ls ++ rs]
         --        | _ => rsmalls.map fun r' => ls ++ [r'] ++ rs
       let ixs := List.range (xs.length)
       ixs.map fun i => shrinkIth xs i

    

-- | returns minimal counterexample along with error
def minimizeCounterexample [Shrinkable α] (a: α) (p: α -> TestResult): α × String :=
  let rec go (xs: List α): α × String:= 
    -- assert! p a == False
    match xs with
    | [] => 
      match p a with
      | TestResult.success => (a, "ERROR: MINIMAL COUNTEREXAMPLE SUCCEEDED ON INPUT")
      | TestResult.failure err => (a, err)
    | x::xs => 
      match p x with
      | TestResult.failure err => (x, err)
      | TestResult.success => go xs
  go (Shrinkable.shrink a)



-- | return some () on success.
def testRandom [ToString α] [Shrinkable α] (name: String) (ra: Rand α) (p: α -> TestResult): IO TestResult := do
   let total := 120
   let rec go (n: Nat) : RandIO TestResult :=  do
     match n with
     | 0 => return TestResult.success
     | Nat.succ n' => do 
           let a <- liftRand2RandIO $ ra
           match p a with
           | TestResult.success => do
                 liftIO2RandIO ∘ IO.eprint $ 
                      "\r                                                         "
                 liftIO2RandIO ∘ IO.eprint $ 
                      "\rsucceeded test [" ++ toString (total-n+1) ++ "/" ++ toString total ++ "]"
                 go n' 
           | TestResult.failure err => do
              let (a, err) := minimizeCounterexample a p
              liftIO2RandIO $ IO.eprintln $ "\nfailed at counter-example:" 
              liftIO2RandIO $ IO.eprintln $ toString a
              liftIO2RandIO $ IO.eprintln $ err
              return TestResult.failure err

   IO.eprintln $ "\n---[" ++ name ++ "]---"
   IO.eprint $ "running tests... [0/" ++ toString total ++ "]"
   let (out, _) <- go total (mkStdGen 0)
   match out with
   | TestResult.success => IO.eprintln "\nPassed all tests"
   | TestResult.failure _ => IO.eprintln "\nFailed test"
   return out

def testExhaustive (ra: Rand a) (p: a -> OptionM Unit) (depth: Int): IO Bool := do
   return true


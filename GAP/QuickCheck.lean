import Init.Data.UInt
import Init.Data.Random
-- import Init.Data.UInt.Bitwise

open Std

  
inductive TestResult
| success
| failure

abbrev Rand α := StdGen -> α × StdGen
abbrev RandIO α := StdGen -> IO (α × StdGen)


def liftRand (ma: Rand α): RandIO α := 
  fun gen => return (ma gen)

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

        




-- | return some () on success.
def testRandom [ToString α] (ra: Rand α) (p: α -> TestResult): IO TestResult := do
   let total := 120
   let rec go (n: Nat) : RandIO TestResult :=  do
     match n with
     | 0 => return TestResult.success
     | Nat.succ n' => do 
           let a <- liftRand ra n
           match p (ra n) with
           | TestResult.success => do
                 IO.eprint $ "\rsucceeded test [" ++ toString (total - n + 1) ++ "/" ++ toString total ++ "]"
                 go n' 
           | TestResult.failure => do
              IO.eprintln $ "failed at counter-example(seed= " ++ toString n ++ "): " ++ toString a
              return TestResult.failure

   IO.eprintln "\n---"
   IO.eprint $ "running tests... [0/" ++ toString total ++ "]"
   let out := evaluateRand (go total)
   match out with
   | TestResult.success => IO.eprintln "\nPassed all tests"
   | TestResult.failure => IO.eprintln "\nFailed test"
   return out

def testExhaustive (ra: Rand a) (p: a -> OptionM Unit) (depth: Int): IO Bool := do
   return true


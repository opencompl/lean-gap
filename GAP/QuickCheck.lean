import Init.Data.UInt
import Init.Data.Random
-- import Init.Data.UInt.Bitwise

open Std

  
inductive TestResult
| success
| failure

abbrev Rand α := StdGen -> α × StdGen
abbrev RandIO α := StdGen -> IO (α × StdGen)

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

        




-- | return some () on success.
def testRandom [ToString α] (ra: Rand α) (p: α -> TestResult): IO TestResult := do
   let total := 120
   let rec go (n: Nat) : RandIO TestResult :=  do
     match n with
     | 0 => return TestResult.success
     | Nat.succ n' => do 
           let a <- liftRand2RandIO $ ra
           match p a with
           | TestResult.success => do
                 liftIO2RandIO $ 
                    IO.eprint $ "\rsucceeded test [" ++ toString (total - n + 1) ++ "/" ++ toString total ++ "]"
                 go n' 
           | TestResult.failure => do
              liftIO2RandIO $ 
                IO.eprintln $ "failed at counter-example(seed= " ++ toString n ++ "): " ++ toString a
              return TestResult.failure

   IO.eprintln "\n---"
   IO.eprint $ "running tests... [0/" ++ toString total ++ "]"
   let (out, _) <- go total (mkStdGen 0)
   match out with
   | TestResult.success => IO.eprintln "\nPassed all tests"
   | TestResult.failure => IO.eprintln "\nFailed test"
   return out

def testExhaustive (ra: Rand a) (p: a -> OptionM Unit) (depth: Int): IO Bool := do
   return true


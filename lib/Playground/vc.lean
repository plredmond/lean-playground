import Init.Data.Array.Lemmas

axiom Array.local_size_zipWith {α β γ} (as : Array α) (bs : Array β) (f : α → β → γ) :
    (as.zipWith bs f).size = min as.size bs.size

theorem Array.local_size_set {α} (a : Array α) (i : Fin a.size) v :
    (a.set i v).size = a.size :=
    by simp

-- -- --

structure Pid (n : Nat) : Type where
    pid : Fin n
    deriving Repr

#eval (Pid.mk 0 : Pid 3)

structure VectorClock (n : Nat) : Type where
    vc : Array Nat
    isSized : vc.size = n
    deriving Repr

def VectorClock.empty {n} : VectorClock n :=
    { vc := (List.replicate n 0).toArray
    , isSized := by simp
    }

-- "@" symbol indicates that all the implicits will be provided explicitly
#eval @VectorClock.empty 3

def VectorClock.tick {n} (v : VectorClock n) (p : Pid n) : VectorClock n :=
    let i := Fin.cast v.isSized.symm p.pid -- kyle miller says to use Fin.cast (mathlib4) for this b/c it has more theorems around it than ▸ and cast
    let c := v.vc[i].succ
    { v with
        vc := v.vc.set i c
        isSized := (v.vc.size_set i c _).trans v.isSized
    }

#eval (@VectorClock.empty 3).tick (Pid.mk 1)

def VectorClock.merge {n} (a b : VectorClock n) : VectorClock n :=
    { vc := a.vc.zipWith b.vc max
    , isSized := by simp [Array.size_zipWith a.vc b.vc _, a.isSized, b.isSized]
    }

instance {n} : LE (VectorClock n) where
    le a b := sorry -- need a ∧ but for a sequence?
#check Array.all

-- TODO lessthan
-- TODO concurrent

-- TODO theorem: describe how tick and merge change things in terms of
-- leq/lt/conc; e.g. (a ≤ merge a b) ∧ (b ≤ merge a b)

structure Process (n : Nat) : Type where
    pid : Pid n
    vc : VectorClock n

def Process.new {n} (p : Pid n) : Process n :=
    { pid := p
    , vc := VectorClock.empty
    -- TODO delay queue
    }

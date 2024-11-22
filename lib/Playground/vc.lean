axiom size_zipWith {α β γ} (as : Array α) (bs : Array β) (f : α → β → γ) :
    (as.zipWith bs f).size = min as.size bs.size
    -- FIXME use the version of this in stdlib (batteries)

theorem size_set (a : Array α) i v : (a.set i v).size = a.size :=
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

def VectorClock.empty : VectorClock n :=
    { vc := (List.replicate n 0).toArray
    , isSized := by simp
    }

#eval @VectorClock.empty 3

def VectorClock.tick (v : VectorClock n) (p : Pid n) : VectorClock n :=
    -- FIXME kyle miller says to use Fin.cast (mathlib4) for this b/c it has
    -- more theorems around it than ▸ and cast
    let i := v.isSized.symm ▸ p.pid
    let c := v.vc[i].succ
    { v with
        vc := v.vc.set i c
        isSized := (v.vc.size_set i c).trans v.isSized
    }

#eval (@VectorClock.empty 3).tick (Pid.mk 0)

def VectorClock.merge (a b : VectorClock n) : VectorClock n :=
    { vc := a.vc.zipWith b.vc max
    , isSized := by simp [size_zipWith a.vc b.vc _, a.isSized, b.isSized]
    }

instance : LE (VectorClock n) where
    le a b := sorry -- need a ∧ but for a sequence?
#check Array.all

-- TODO lessthan
-- TODO concurrent

-- TODO theorem: describe how tick and merge change things in terms of
-- leq/lt/conc; e.g. (a ≤ merge a b) ∧ (b ≤ merge a b)

structure Process (n : Nat) : Type where
    pid : Pid n
    vc : VectorClock n

def Process.new (p : Pid n) : Process n :=
    { pid := p
    , vc := VectorClock.empty
    -- TODO delay queue
    }

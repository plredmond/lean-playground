import Mathlib.Data.Set.Basic

-- simple non-live consensus algorithm

structure AbstractProtocol (nid : Type) (α : Type) where
    votes : Set (nid × α)
    decisions : Set (nid × α)
    inv_agree (n₁ n₂ v₁ v₂) : (n₁,v₁) ∈ decisions → (n₂,v₂) ∈ decisions → v₁ = v₂
    inv_vote_first (n v) : (n,v) ∈ decisions → (n,v) ∈ votes
    inv_vote_once (n v₁ v₂) : (n,v₁) ∈ votes → (n,v₂) ∈ votes → v₁ = v₂

namespace AbstractProtocol
    abbrev AP := AbstractProtocol

    def init {nid α} : AP nid α :=
        { votes := ∅
        , decisions := ∅
        , inv_agree := by simp
        , inv_vote_first := by simp
        , inv_vote_once := by simp
        }

    def vote {nid α} (node : nid) (val : α) (p : AP nid α) : AP nid α :=
        { p with
            votes := insert (node, val) p.votes
            inv_vote_first := sorry
            inv_vote_once := sorry
        }

    def decide {nid α} (node : nid) (val : α) (p : AP nid α) : AP nid α :=
        let d := insert (node, val) p.decisions
        { p with
            decisions := d
            inv_agree := sorry
            inv_vote_first := sorry
        }

end AbstractProtocol

def Pid (ub : Nat) : Type := Fin ub
def Pid.mk {ub : Nat} : (i : Nat) → (i < ub) → Pid ub := Fin.mk

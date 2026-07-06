/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.SimulateQ

open OracleSpec OracleComp

universe u

namespace AEAD

structure Scheme (m : Type → Type u) [Monad m] (Msg Key AD C : Type) where
  encrypt : Key → AD → Msg → m C
  decrypt : Key → AD → C → Option Msg

def withUnif {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl (unifSpec + spec) (StateT σ ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget (StateT σ ProbComp) + impl

variable {Msg Key AD C : Type} [DecidableEq Msg] [SampleableType Key]
  [DecidableEq AD] [DecidableEq C]

def CorrectExp (aead : Scheme ProbComp Msg Key AD C) (msg : Msg) (ad : AD) : ProbComp Bool := do
  let k ← $ᵗ Key
  let c ← aead.encrypt k ad msg
  pure (decide (aead.decrypt k ad c = some msg))

def PerfectlyCorrect (aead : Scheme ProbComp Msg Key AD C) : Prop :=
  ∀ msg ad, Pr[= true | CorrectExp aead msg ad] = 1

structure IND_CPA_Adversary (_aead : Scheme ProbComp Msg Key AD C) where
  run : OracleComp (unifSpec + ((AD × Msg × Msg) →ₒ C)) Bool

def cpaImpl (aead : Scheme ProbComp Msg Key AD C) (k : Key) (b : Bool) :
    QueryImpl (unifSpec + ((AD × Msg × Msg) →ₒ C)) ProbComp :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) +
    fun p : AD × Msg × Msg => (aead.encrypt k p.1 (if b then p.2.2 else p.2.1) : ProbComp C)

def IND_CPA_Game (aead : Scheme ProbComp Msg Key AD C)
    (A : IND_CPA_Adversary aead) : ProbComp Bool := do
  let k ← $ᵗ Key
  let b ← $ᵗ Bool
  let b' ← simulateQ (cpaImpl aead k b) A.run
  pure (b' == b)

noncomputable def IND_CPA_Advantage (aead : Scheme ProbComp Msg Key AD C)
    (A : IND_CPA_Adversary aead) : ℝ :=
  |(Pr[= true | IND_CPA_Game aead A]).toReal - 1 / 2|

def ctxtImpl (aead : Scheme ProbComp Msg Key AD C) (k : Key) :
    QueryImpl ((AD × Msg) →ₒ C) (StateT (List (AD × C)) ProbComp) :=
  fun p => do
    let c ← (aead.encrypt k p.1 p.2 : ProbComp C)
    modify (fun log => log ++ [(p.1, c)])
    pure c

structure IND_CTXT_Adversary (_aead : Scheme ProbComp Msg Key AD C) where
  run : OracleComp (unifSpec + ((AD × Msg) →ₒ C)) (AD × C)

def IND_CTXT_Game (aead : Scheme ProbComp Msg Key AD C)
    (A : IND_CTXT_Adversary aead) : ProbComp Bool := do
  let k ← $ᵗ Key
  let (forge, log) ← (simulateQ (withUnif (ctxtImpl aead k)) A.run).run []
  pure ((aead.decrypt k forge.1 forge.2).isSome && decide (forge ∉ log))

noncomputable def IND_CTXT_Advantage (aead : Scheme ProbComp Msg Key AD C)
    (A : IND_CTXT_Adversary aead) : ℝ :=
  (Pr[= true | IND_CTXT_Game aead A]).toReal

end AEAD

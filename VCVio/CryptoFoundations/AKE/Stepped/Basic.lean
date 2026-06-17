/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.AKE.Game

open OracleSpec OracleComp

namespace Stepped

variable {Msg SendK RecvK W : Type}

structure Party (In W Out : Type) where
  State : Type
  init : In → ProbComp (State × Option W)
  step : State → W → ProbComp (State × (W ⊕ Out))

structure Transcript (W : Type) where
  entries : List (W × ℕ)

structure Session (σ W : Type) where
  state : σ
  transcript : Transcript W

def interleave : Bool → List (ℕ × ℕ) → List ℕ
  | _, [] => []
  | ab, (a, b) :: rest => (if ab then [a, b] else [b, a]) ++ interleave (!ab) rest

def Matching (oracleLeadsFirst : Bool) (T Tstar : Transcript W) : Prop :=
  T.entries.map Prod.fst = Tstar.entries.map Prod.fst ∧
    List.IsChain (· < ·)
      (interleave oracleLeadsFirst ((T.entries.map Prod.snd).zip (Tstar.entries.map Prod.snd)))

instance [DecidableEq W] (b : Bool) (T Tstar : Transcript W) :
    Decidable (Matching b T Tstar) := by
  unfold Matching
  infer_instance

def pingPong [DecidableEq W] (oracleLeadsFirst : Bool)
    (oracleTrs : List (Transcript W)) (challengeTr : Transcript W) : Bool :=
  oracleTrs.any fun T => decide (Matching oracleLeadsFirst T challengeTr)

def recordOne (tr : Transcript W) (w : W) (clock : ℕ) : Transcript W × ℕ :=
  (⟨tr.entries ++ [(w, clock)]⟩, clock + 1)

def recordOpt (tr : Transcript W) : Option W → ℕ → Transcript W × ℕ
  | none, clock => (tr, clock)
  | some w, clock => recordOne tr w clock

namespace MTP

structure Scheme (Msg SendK RecvK W : Type) where
  rounds : ℕ
  setup : ProbComp (SendK × RecvK)
  sender : Party (SendK × Msg) W Unit
  receiver : Party RecvK W (Option Msg)

end MTP

end Stepped

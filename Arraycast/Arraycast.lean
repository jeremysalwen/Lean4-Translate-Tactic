import Lean
import Std.Data.Array.Init.Lemmas
import Std.Data.Array.Lemmas
import Mathlib.Tactic.Find
import Mathlib.Tactic.Simps.Basic
import Lean.Elab.Term
import Arraycast.SimpAttrs
import Arraycast.Translate

open Lean Meta Elab Term Lean.Meta Tactic

#find Array.data _ = _

lemma List.toArray_data (a:Array α): (List.toArray a.data) = a := by simp

#translateSimpLemmas Array Array.data List.toArray List.toArray_data Array.data_toArray

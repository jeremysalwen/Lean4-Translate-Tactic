import Lean
import Std.Data.Array.Init.Lemmas
import Std.Data.Array.Lemmas
import Mathlib.Tactic.Find
import Mathlib.Tactic.Simps.Basic
import Lean.Elab.Term
import Arraycast.Arraycast

lemma Array.map_push (f: α → β) (a:Array α) (e:α): map f (a.push e) = (map f a).push (f e) := by
  -- Converts array operations to list operations.
  simp only [array_to_list]
  -- We can now prove the resulting statement using simp (for example)
  simp
  
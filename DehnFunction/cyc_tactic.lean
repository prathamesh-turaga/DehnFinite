import Lean.Elab.Tactic

open Lean Meta Elab Tactic


@[tactic applyEmbeddingRel]
def evalApplyEmbeddingRel : Tactic := fun _stx => do
  liftMetaTactic fun goal => do
    let thm ← mkConst `embedding_rel
    let r ← goal.rewrite thm (symm := false)
    if r.replaced then
      pure [r.goal]
    else
      let r' ← goal.rewrite thm (symm := true)
      if r'.replaced then
        pure [r'.goal]
      else
        throwError "apply_embedding_rel: could not rewrite using embedding_rel"

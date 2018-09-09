import tactic.basic
import .lock_tactic_state
import .mllist

universes u

open tactic
open mllist

meta def kabstracter'
  (pattern : tactic (expr × expr × list expr))
  (lhs_replacer : list expr → tactic expr) :
  expr × list (expr × (list expr)) → tactic (expr × list (expr × (list expr)))
| p := do
  (t, L) ← pure p,
  (e, e_type, mvars) ← pattern,
  t' ← kabstract t e semireducible,
  -- trace "kabstract:",
  -- trace t',
  guard t'.has_var,
  w ← mk_meta_var e_type,
  let t'' := t'.instantiate_var w,
  mvars' ← mvars.mmap instantiate_mvars,
  return (t'', (w, mvars) :: L)

meta def kabstracter 
  (pattern : tactic (expr × expr × list expr))
  (lhs_replacer : list expr → tactic expr) (t : expr) : tactic (mllist tactic (expr × list (expr × list expr))) :=
mllist.fix (kabstracter' pattern lhs_replacer) (t, [])

meta def substitutions_core : expr → list expr → 
  tactic (tactic (expr × expr × list expr) × (list expr → tactic expr) × (list expr → tactic expr))
| (expr.pi n bi d b) types := 
  do substitutions_core b (d :: types)          
| `(%%lhs = %%rhs) types := 
  do let fresh_mvars := (do mvars ← types.mmap mk_meta_var,
                           let pattern := lhs.instantiate_vars mvars,
                           ty ← infer_type pattern,
                           return (pattern, ty, mvars)),
     let lhs_replacer : list expr → tactic expr := (λ values, return (lhs.instantiate_vars values)),
     let rhs_replacer : list expr → tactic expr := (λ values, return (rhs.instantiate_vars values)),
     return (fresh_mvars, lhs_replacer, rhs_replacer)
| _ _ := failed

/-- Given a lemma `eq`, returns three tactics.
    1) returning `(lhs, ty, mvars)` where `lhs` is a copy of the left hand side of the lemma, with
    variables replaced by fresh metavariables `mvars`.
    2) taking a list of expressions, and returning `lhs'`, the left hand side with variables
    instantiated with these values.
    3) as with 2), but for the right hand side. -/
meta def substitutions (eq : expr) : tactic (tactic (expr × expr × list expr) × (list expr → tactic expr) × (list expr → tactic expr)) :=
substitutions_core eq []

meta def mvars_to_var (e : expr) : expr :=
e.replace (λ e n, if e.is_meta_var then some (expr.var n) else none)

meta def do_substitutions
  (eq : expr)
  (t_original : expr)
  (lhs rhs : list expr → tactic expr)
  (t_abstracted : expr)
  (rewrite_mvar : expr × list expr)
  (restore_mvars : list (expr × list expr)) : tactic (expr × tactic expr × list expr) :=
lock_tactic_state $
do -- We first restore all the "other" metavariables to their original values.
   restore_mvars.mmap (λ p, do l ← lhs p.2, unify p.1 l),
   t_restored ← instantiate_mvars t_abstracted,

   -- r' is the value of the remaining metavariable, after applying the lemma.
   r' ← rhs rewrite_mvar.2,

   -- We now begin constructing the `eq.rec` proof of equality. In fact, we don't construct it here,
   -- we just construct a tactic that can produce it on demand!
   let proof_tactic : tactic expr := do {
    -- r is the original value of the remaining metavariable
    r ← lhs rewrite_mvar.2,

    -- The lemma itself proves `r = r'`.
    let inner_proof := rewrite_mvar.2.reverse.foldl (λ f x : expr, f x) eq,

    -- Next we compute the motive.
    let t_with_var := mvars_to_var t_restored,
    n ← mk_fresh_name,
    eq ← to_expr ``(%%t_with_var = %%t_original),
    ty ← infer_type r,
    let C := expr.lam n binder_info.default ty eq,

    -- ... and prepare the actual proof.
    refl ← mk_eq_refl t_original,
    proof ← to_expr ```(@eq.rec _ %%r %%C %%refl _ %%inner_proof),
    infer_type proof,
    return proof
   },
   -- Finally we finish rewriting the expression
   unify rewrite_mvar.1 r',
   result ← instantiate_mvars t_restored,

   metas : list expr ← rewrite_mvar.2.mfilter (λ m, do r ← is_assigned m, return ¬ r), -- FIXME check if there are any remaining metavariables
   return (result, proof_tactic, metas)

meta def all_rewrites_core (t eq : expr) : tactic (mllist tactic (expr × tactic expr × list expr)) :=
do ty ← infer_type eq,
  (matcher, lhs, rhs) ← substitutions ty,
  L ← kabstracter matcher lhs t,
  L ← L.mmap (λ p, do_substitutions eq t lhs rhs p.1 p.2.head p.2.tail),
  return L

meta def all_rewrites' (t eq : expr) : tactic (list (expr × expr × list expr)) :=
do L ← all_rewrites_core t eq,
   L' ← L.mmap (λ p, do r ← p.2.1, return (p.1, r, p.2.2)),
   L'.force
  
constant f (x : ℕ) (y : ℕ) : ℕ
axiom fx (n : ℕ) (m : ℕ) : f n m = f 17 19

example : [f 1 2, 3, f 2 5] = [f 1 2, 3, f 2 5] :=
begin
(do `(%%lhs = %%rhs) ← target,
    eq ← mk_const `fx,
    r ← all_rewrites' lhs eq,
    trace r),
refl
end

meta structure rewrite_all_cfg extends rewrite_cfg :=
(discharger : tactic unit := skip)
(simplifier : expr → tactic (expr × expr) := λ e, failed) -- FIXME get rid of this

meta def all_rewrites (r : expr × bool) (t : expr) (cfg : rewrite_all_cfg := {}): tactic (list (expr × expr)) :=
do e ← if r.2 then mk_eq_symm r.1 else return r.1,
   results ← all_rewrites' t e,
   -- TODO use the discharger to clear remaining metavariables
   let results := results.filter (λ p, p.2.2 = []),
   let results := results.map (λ p, (p.1, p.2.1)),
   return results


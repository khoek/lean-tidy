-- import .types

-- open interactive interactive.types expr tactic

-- variables {α β γ δ : Type}

-- namespace tidy.rewrite_search

-- private meta def hand : sided_pair string := ⟨"lhs", "rhs"⟩

-- meta def nth_rule (cfg : config) (i : ℕ) : expr × bool := (cfg.rs.nth i).iget

-- meta def pp_rule (r : expr × bool) : tactic string :=
--   do pp ← pretty_print r.1, return $ (if r.2 then "←" else "") ++ pp

-- meta def how.to_rewrite (cfg : config) : how → option (expr × bool)
-- | (how.rewrite index _ _) := nth_rule cfg index
-- | _ := none

-- meta def how.explain_using_location (cfg : config) (s : side) : how → tactic (option string)
-- | (how.rewrite index location _) := do
--   rule ← pp_rule $ nth_rule cfg index,
--   return $ some ("nth_rewrite_" ++ hand.get s ++ " " ++ to_string location ++ " " ++ rule)
-- | _ := return none

-- meta def using_location.explain_rewrites (cfg : config) (s : side) (steps : list how) : tactic string := do
--   rules ← steps.mmap $ λ h : how, option.to_list <$> h.explain_using_location cfg s,
--   return $ string.intercalate ",\n" rules.join

-- namespace using_conv

-- open app_addr

-- meta inductive proof_step
-- | conv (parent : option app_addr) (root func arg : list (how × app_addr)) : proof_step
-- | other : how → proof_step

-- meta def build_rw_list (cfg : config) (hs : list how) : tactic string := do
--   rws ← (hs.filter_map (how.to_rewrite cfg)).mmap pp_rule,
--   return $ string.lconcat $ list.join $ rws.map $ λ rw, ["rw ", rw, ", "]

-- meta def addr.to_conv_tactics : option app_addr → string
-- | none            := ""
-- | (some root)     := ""
-- | (some (func p)) := addr.to_conv_tactics p ++ "congr, "
-- | (some (arg p))  := addr.to_conv_tactics p ++ "skip, "

-- meta def proof_step.explain (cfg : config) (s : side) : proof_step → tactic string
-- | (proof_step.conv parent r f a) := do
--   if r.length > 0 then
--     -- TODO is this possible?
--     fail "trying to explain root level rewrite!"
--   else do
--     f_rws ← build_rw_list cfg $ f.map prod.fst,
--     a_rws ← build_rw_list cfg $ a.map prod.fst,
--     return $ "conv { to_" ++ hand.get s ++ ", congr, " ++ addr.to_conv_tactics parent ++ f_rws ++ "skip, " ++ a_rws ++ " }"
-- | (proof_step.other h) := return ""

-- private meta def from_family_aux : list (how × option app_addr) → list (how × app_addr) × list (how × app_addr) × list (how × app_addr)
-- | [] := ([], [], [])
-- | (v :: rest) :=
--   let t := match v with
--   | (h, none)          := ([], [], [])
--   | (h, some root)     := ([(h, app_addr.root)], [], [])
--   | (h, some (func a)) := ([], [(h, app_addr.func a)], [])
--   | (h, some (arg a))  := ([], [], [(h, app_addr.arg a)])
--   end in
--   let ts := from_family_aux rest in
--   (t.1 ++ ts.1, t.2.1 ++ ts.2.1, t.2.2 ++ ts.2.2)

-- meta def proof_step.from_family (l : list (how × option app_addr)) : list proof_step :=
-- match l with
-- | [] := []
-- | ((h, none) :: rest) := l.map $ λ p, proof_step.other p.1
-- | ((h, some addr) :: rest) := do
--   let t := from_family_aux l,
--   return $ proof_step.conv addr.func_parent t.1 t.2.1 t.2.2
-- end

-- private meta def sort_by_parent_aux : option app_addr → list (how × option app_addr) → list how → tactic (list proof_step)
-- | prev_parent curr [] := return $ if curr.length = 0 then [] else proof_step.from_family curr
-- | prev_parent curr (h :: rest) := do
--   (addr, addr_parent) ← match h with
--   | how.rewrite index _ addr := do
--     addr ← addr,
--     pure $ (some addr, addr.func_parent)
--   | _ := return (none, none)
--   end,
--   trace format!"{addr_parent.to_list.map app_addr.to_string} vs {prev_parent.to_list.map app_addr.to_string}",
--   (head, curr) ← pure $ if addr_parent = prev_parent then
--     ([], curr.concat (h, addr))
--   else
--     (if curr.length = 0 then [] else proof_step.from_family curr, [(h, addr)]),
--   list.append head <$> sort_by_parent_aux addr_parent curr rest

-- meta def sort_by_parent : list how → tactic (list proof_step) :=
--   sort_by_parent_aux none []

-- meta def explain_rewrites (cfg : config) (s : side) (hows : list how) : tactic string := do
--   hows.mmap' $ λ h, match h with
--   | how.rewrite idx _ addr := do addr ← addr, pp ← pp_rule $ nth_rule cfg idx, trace format!"{pp} : {addr.to_string}"
--   | _ := skip
--   end,
--   trace "\n",
--   steps ← sort_by_parent hows,
--   string.intercalate ",\n" <$> steps.mmap (proof_step.explain cfg s)

-- end using_conv

-- meta def explain_rewrites_concisely (steps : list (expr × bool)) (needs_refl : bool) : tactic string := do
--   rules ← string.intercalate ", " <$> steps.mmap pp_rule,
--   return $ "erw [" ++ rules ++ "]" ++ (if needs_refl then ", refl" else "")

-- -- fails if we can't just use rewrite
-- -- otherwise, returns 'tt' if we need a `refl` at the end
-- meta def check_if_simple_rewrite_succeeds (rewrites : list (expr × bool)) (goal : expr) : tactic bool :=
-- lock_tactic_state $ do
--   m ← mk_meta_var goal,
--   set_goals [m],
--   rewrites.mmap' $ λ q, rewrite_target q.1 {symm := q.2, md := semireducible},
--   (reflexivity reducible >> return ff) <|> (reflexivity >> return tt)

-- meta def proof_unit.rewrites (u : proof_unit) (cfg : config) : list (expr × bool) :=
--   u.steps.filter_map $ how.to_rewrite cfg

-- -- TODO rewrite this to use conv!
-- meta def proof_unit.explain (u : proof_unit) (cfg : config) : tactic string := do
--   -- TODO We could try to merge adjacent proof units or something more complicated.
--   -- Currently we only try the "most coarse" (whole proof) and "most fine" (proof_unit
--   -- level) levels of simplication, not anywhere in between.
--   (do
--     goal ← infer_type u.proof,
--     let rewrites := u.rewrites cfg,
--     needs_refl ← check_if_simple_rewrite_succeeds rewrites goal,
--     explain_rewrites_concisely rewrites needs_refl
--   )
--   -- <|> using_location.explain_rewrites cfg u.side u.steps
--   <|> using_conv.explain_rewrites cfg u.side u.steps

-- meta def explain_proof_full (cfg : config) : list proof_unit → tactic string
-- | [] := return ""
-- | (u :: rest) := do
--   -- This is an optimisation: don't use transitivity for the last unit, since
--   -- it neccesarily must be redundant.
--   head ← if rest.length = 0 ∨ u.side = side.L then pure [] else (do
--     n ← infer_type u.proof >>= rw_equation.rhs >>= pretty_print,
--     pure $ ["transitivity " ++ n]
--   ),

--   unit_expl ← u.explain cfg,
--   rest_expl ← explain_proof_full rest,
--   let expls := (head ++ [unit_expl, rest_expl]).filter $ λ t, ¬(t.length = 0),
--   return $ string.intercalate ",\n" expls

-- meta def explain_proof_concisely (cfg : config) (proof : expr) (l : list proof_unit) : tactic string := do
--   let rws : list (expr × bool) := list.join $ l.map (λ u, do
--     (r, s) ← u.rewrites cfg,
--     return (r, if u.side = side.L then s else ¬s)
--   ),
--   goal ← infer_type proof,
--   needs_refl ← check_if_simple_rewrite_succeeds rws goal,
--   explain_rewrites_concisely rws needs_refl

-- meta def explain_search_result (cfg : config) (proof : expr) (units : list proof_unit) : tactic string := do
--   if cfg.trace then do
--     pp ← pretty_print proof,
--     trace format!"rewrite_search found proof:\n{pp}"
--   else skip,

--   explanation ← explain_proof_concisely cfg proof units <|> explain_proof_full cfg units,
--   if cfg.trace_result then trace $ "/- `rewrite_search` says -/\n" ++ explanation
--   else skip,
--   return explanation

-- end tidy.rewrite_search
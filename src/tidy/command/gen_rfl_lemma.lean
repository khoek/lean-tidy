import data.list
import tidy.lib.parser
import tidy.pretty_print

open lean lean.parser
open interactive interactive.types

open exceptional
open declaration

meta def chop_app : expr → option (name × list level × list expr)
| (expr.const n us) := some (n, us, [])
| (expr.app e v) :=
  match chop_app e with
  | none   := none
  | some (n, us, vs) := some (n, us, (v :: vs))
  end
| _ := none

meta def strip_pi_binders_aux : list (name × expr × binder_info) → expr → list (name × expr × binder_info) × expr
| curr (expr.pi var_n bi var_type rest) :=
  strip_pi_binders_aux (curr.concat (var_n, var_type, bi)) rest
| curr ex := (curr, ex)

meta def strip_pi_binders : expr → list (name × expr × binder_info) × expr :=
  strip_pi_binders_aux []

meta def strip_lam_binders_aux : list (name × expr × binder_info) → expr → list (name × expr × binder_info) × expr
| curr (expr.lam var_n bi var_type rest) :=
  strip_lam_binders_aux (curr.concat (var_n, var_type, bi)) rest
| curr ex := (curr, ex)

meta def strip_lam_binders : expr → list (name × expr × binder_info) × expr :=
  strip_lam_binders_aux []

meta def build_pi_binders : list (name × expr × binder_info) → expr → expr
| ((var_n, var_type, bi) :: rest) ex := expr.pi var_n bi var_type $ build_pi_binders rest ex
| [] ex := ex

meta def build_lam_binders : list (name × expr × binder_info) → expr → expr
| ((var_n, var_type, bi) :: rest) ex := expr.lam var_n bi var_type $ build_lam_binders rest ex
| [] ex := ex

meta def instantiate_binder_list_vars_aux : list (name × expr × binder_info) → list (name × expr × binder_info) → list (name × expr × binder_info)
| seen [] := seen
| seen ((n, e, bi) :: rest) :=
  let e := e.instantiate_vars $ seen.reverse.map $ λ v, expr.const v.1 [] in
  instantiate_binder_list_vars_aux (seen.concat (n, e, bi)) rest

meta def instantiate_binder_list_vars : list (name × expr × binder_info) → list (name × expr × binder_info) :=
  instantiate_binder_list_vars_aux []

-- meta def cut_vars_at_const_aux (target : name) : list (name × expr × binder_info) → list (name × expr × binder_info) → tactic (list (name × expr × binder_info) × (name × expr × binder_info) × list (name × expr × binder_info))
-- | seen [] := tactic.trace "couldn't find the target expr!" >> interaction_monad.failed
-- | seen ((n, e, bi) :: rest) :=
--   match extract_const e with
--   | none := cut_vars_at_const_aux (seen.concat (n, e, bi)) rest
--   | some m :=
--     if target = m then
--       return (seen, (n, e, bi), rest)
--     else
--       cut_vars_at_const_aux (seen.concat (n, e, bi)) rest
--   end

-- meta def cut_vars_at_const (target : name) : list (name × expr × binder_info) → tactic (list (name × expr × binder_info) × (name × expr × binder_info) × list (name × expr × binder_info)) :=
--   cut_vars_at_const_aux target []

meta def expr_type : expr → string
| (expr.var n)               := "var" ++ to_string n
| (expr.sort _)              := "sort"
| (expr.const n _)           := "`"++to_string n
| (expr.mvar _ _ _)          := "mvar"
| (expr.local_const _ _ _ _) := "local_const"
| (expr.app e f)             := "app (" ++ expr_type e ++ ") (" ++ expr_type f ++ ")"
| (expr.lam _ _ _ _)         := "lam"
| (expr.pi _ _ _ _)          := "pi"
| (expr.elet _ _ _ _)        := "elet"
| (expr.macro _ _)           := "macro"

meta def binder_info.brackets : binder_info → string × string
| binder_info.default  := ("(", ")")
| binder_info.implicit := ("{", "}")
| binder_info.inst_implicit := ("[", "]")
| bi := ("?", "?" ++ repr bi)

meta def downgrade_variable : name × expr × binder_info → option (name × expr × binder_info)
| (n, e, binder_info.default) := some (n, e, binder_info.implicit)
| (_, _, _) := none

meta def drop_implicit_variable : name × expr × binder_info → option (name × expr × binder_info)
| (n, e, binder_info.default) := some (n, e, binder_info.implicit)
| (_, _, _) := none

meta def styleize_variable : name × expr × binder_info → string
| (n, e, bi) := let brackets := bi.brackets in
  brackets.1 ++ to_string n ++ " : " ++ to_string e ++ brackets.2

meta def build_invocation_arg : name × expr × binder_info → option string
| (n, _, binder_info.default) := some $ to_string n
| (n, _, _) := none

meta def string.lconcat : list string → string
| [] := ""
| (s :: rest) := s ++ string.lconcat rest

meta def build_invocation_args (l : list (name × expr × binder_info)) : string :=
  string.lconcat $ (l.filter_map build_invocation_arg).intersperse " "

-- TODO scope
-- meta def generate_lemma (def_name : name) (us : list name) (def_type : expr) (field : name) : lean.parser unit := do
--   (def_vars, def_val) ← pure $ strip_pi_binders def_type,
--   let def_vars_params := def_vars.map styleize_variable,
--   tactic.trace format!"def vars:{def_vars_params}",

--   let inst_val := def_val.instantiate_vars $ def_vars.reverse.map (λ v, expr.const v.1 []),
--   tactic.trace format!"instval: {inst_val.to_raw_fmt}",
--   tactic.trace format!"defval: {def_val.to_raw_fmt}",


--   tactic.trace format!"defval: {def_val}",
--   obj_name ← match extract_const def_val with
--   | none := interaction_monad.fail "whaaaat"
--   | some t := pure t
--   end,
--   tactic.trace format!"obj_name: {obj_name}",

--   let full_field_name := obj_name ++ (name.mk_string (field.to_string ++ "'") name.anonymous),
--   c ← tactic.mk_const full_field_name,
--   field_type ← tactic.infer_type c,
--   tactic.trace format!"field_type: {field_type}",
--   (field_vars, field_val) ← pure $ strip_pi_binders field_type,

--   -- TODO Properly resolve these using the def instead of just swapping them out.
--   -- TODO (this NEEDS to happen)
--   (_, obj, field_params) ← cut_vars_at_const obj_name field_vars,
--   let field_params := def_vars.filter_map drop_implicit_variable ++ [obj] ++ field_params,
--   let field_params := instantiate_binder_list_vars field_params,
--   tactic.trace format!"field_params: {field_params.map styleize_variable}",

--   let def_invocation := "(" ++ to_string def_name ++ " " ++ build_invocation_args def_vars ++ ")." ++ to_string field ++ " " ++ build_invocation_args field_vars,
--   tactic.trace format!"def invoke:{def_invocation}",

--   tactic.trace field_type,
--   emit_code_here $ "\n@[simp] lemma " ++ to_string def_name ++ "_" ++ to_string field ++ " " ++ to_string def_type

meta def count_apps : expr → tactic ℕ
| (expr.const _ _) := return 0
| (expr.app e _)   := count_apps e
| _                := tactic.fail "not an app or const!"

meta def pop_n_last_apps_get_arg : expr → ℕ → tactic expr
| (expr.app _ f) 0 := return f
| (expr.app e _) n := pop_n_last_apps_get_arg e (n - 1)
| _ _              := tactic.fail "not an app!"

meta def extract_nth_structure_field (st : expr) (n : ℕ) : tactic expr := do
  len ← count_apps st,
  pop_n_last_apps_get_arg st (len - n)

meta def apply_to_expr : list expr → expr → expr
| [] ex          := ex
| (p :: rest) ex := apply_to_expr rest (expr.app ex p)

meta def mk_explicit_param_list_starting_at_aux : ℕ → list (name × expr × binder_info) → list expr
| k []                                    := []
| k ((n, e, binder_info.default) :: rest) := (expr.var k :: mk_explicit_param_list_starting_at_aux (k + 1) rest)
| k (_ :: rest)                           := mk_explicit_param_list_starting_at_aux (k + 1) rest

meta def mk_explicit_param_list_starting_at (n : ℕ) (l : list (name × expr × binder_info)) : list expr :=
  (mk_explicit_param_list_starting_at_aux n l.reverse).reverse

meta def mk_explicit_param_list (l : list (name × expr × binder_info)) : list expr :=
  (mk_explicit_param_list_starting_at 0 l.reverse).reverse

meta def mk_param_list_starting_at_aux : ℕ → list (name × expr × binder_info) → list expr
| k []                                    := []
| k (_ :: rest) := (expr.var k :: mk_param_list_starting_at_aux (k + 1) rest)

meta def mk_param_list_starting_at (n : ℕ) (l : list (name × expr × binder_info)) : list expr :=
  (mk_param_list_starting_at_aux n l.reverse).reverse

meta def mk_param_list (l : list (name × expr × binder_info)) : list expr :=
  (mk_param_list_starting_at 0 l.reverse).reverse

-- TODO scope
meta def generate_lemma (def_name : name) (us : list name) (def_type : expr) (def_val : expr) (field : name) : tactic environment := do
  (def_type_params, def_type_val) ← pure $ strip_pi_binders def_type,
  (obj_name, obj_name_levels, def_type_app_vars) ← chop_app def_type_val,

  tactic.trace def_type_app_vars,
  -- tactic.trace format!"chopping:{def_type_params.map styleize_variable}",

  e ← tactic.get_env,

  (def_val_params, def_val_core) ← pure $ strip_lam_binders def_val,
  -- tactic.trace def_val_core.to_raw_fmt,
  -- let def_val_core := def_val_core.instantiate_vars $ def_val_params.map $ λ v, expr.const v.1 [],

  let def_proj := obj_name ++ field,
  -- tactic.infer_type (expr.const def_proj []) >>= tactic.trace,
  let primed_proj := (obj_name ++ (name.mk_string (field.to_string ++ "'")) name.anonymous),

  field_val_idx ← match e.is_projection primed_proj with
  | none := interaction_monad.fail "o"
  | some pi := return $ pi.nparams + pi.idx
  end,
  field_val ← extract_nth_structure_field def_val_core field_val_idx,
  (field_val_params, field_val_core) ← pure $ strip_lam_binders field_val,

  field_type ← tactic.infer_type (expr.const primed_proj []),
  (field_type_params, field_type_core) ← pure $ strip_pi_binders field_type,
  (field_type_name, field_type_univ, field_type_app_vars) ← chop_app field_type_core,
  -- tactic.trace $ field_val_params.map styleize_variable,
  -- tactic.trace field_val_core,

  -- tactic.trace $ field_type_params.map styleize_variable,
  tactic.trace field_type_app_vars,
  field_type_vars ← field_type_app_vars.mmap $ λ e,
    match e with
    | expr.var n := do
      e ← def_type_app_vars.nth (n - field_val_params.length - 1),
      return (e.lift_vars 0 field_val_params.length)
    | _ := fail "waaa"
    end,
  -- field_type_vars  field_type_vars,
  let field_type := (apply_to_expr field_type_vars.reverse (expr.const field_type_name field_type_univ)),
  tactic.trace field_type,
  tactic.trace field_type_vars,

  let full_params := def_val_params ++ field_val_params,

  -- Resolve the parameters in the constructor.
  let defn_vars := ((list.range def_type_params.length).map $ λ n, @expr.var tt (n + field_val_params.length)),
  let cnst_vars := def_type_app_vars.map $ λ e, e.lift_vars 0 field_val_params.length,
  -- tactic.trace cnst_params,

  let last_params := mk_param_list field_val_params,
  let lemma_lhs := apply_to_expr defn_vars.reverse (expr.const def_name []),
  let lemma_lhs := apply_to_expr last_params.reverse (expr.app (apply_to_expr cnst_vars.reverse (expr.const def_proj [])) lemma_lhs),
  -- tactic.trace lemma_lhs.to_raw_fmt,
  let lemma_rhs := field_val_core,
  let lemma_core : expr := expr.app (expr.app (expr.app (expr.const `eq [level.of_nat 1]) field_type) lemma_lhs) lemma_rhs,
  -- tactic.trace "core:",
  -- tactic.trace $ expr_type lemma_core,
  -- tactic.trace "",

  let lemma_rfl : expr := apply_to_expr [field_type, lemma_lhs] (expr.const `rfl [level.of_nat 1]),

  let lemma_type := build_pi_binders full_params lemma_core,
  let lemma_val := build_lam_binders full_params lemma_rfl,
  -- pretty_print lemma_type >>= tactic.trace,
  -- pretty_print lemma_val >>= tactic.trace,
  -- tactic.trace lemma_rfl.to_raw_fmt,
  tactic.trace $ build_lam_binders full_params field_type,

-- mk_definition (n : name) (ls : list name) (v : expr) (e : expr)

  e.add $ mk_definition (mk_str_name name.anonymous (to_string def_name ++ "_" ++ to_string field)) [] lemma_type lemma_val

meta def build_lemma (obj_def : name) (field : name) : tactic unit := do
  e ← tactic.get_env,
  match e.get obj_def with
  | exception _ f := fail (f options.mk)
  | success decl :=
    match decl with
    | thm  n us type _     := sorry
    | cnst n us type _     := sorry
    | ax   n us type       := sorry
    | defn n us type val _ _ := do
      e ← generate_lemma n us type val field,
      tactic.set_env e
    end
  end

@[user_command]
meta def gen_rfl_lemma_cmd (d : decl_meta_info) (_ : parse $ tk "gen_rfl_lemma") : lean.parser unit := do
  obj_def ← ident,
  field ← ident,
  build_lemma obj_def field
  -- mk_definition_here_raw n [] none (bn.map $ λ s, "`" ++ to_string s).to_string tt ["simp"]

structure metype (A B : Type) :=
(v : ℕ)

structure a_dummy (C D : Type) :=
(map'      : Π {X Y : Type}, (C → X → Y) → metype C D)

def a_dummy.map {C D : Type} (F : a_dummy C D) {X Y : Type} (f : C → X → Y) : metype C D := F.map' f

def lol (E F : Type) [has_lt ℕ] : a_dummy F E :=
{ map' := λ X Y, λ f, ⟨F, E, 42⟩ }.

-- FIXME pure boilerplate...
@[simp] lemma lol_map2
  (E F : Type) [has_lt ℕ] {X Y : Type} (f : F → X → Y) :
  (lol E F).map f = ⟨F, E, 42⟩ := rfl.

def lol : ff := begin
  build_lemma `lol `map,

end

#check @a_dummy.map

structure x :=
(a : ℕ)

structure y { a : string} :=
(b : string)
(c : string)

def x_1 : x := ⟨2⟩

def y_1 : @y "ff" := ⟨"foo", "bar"⟩

--(app (app (const rfl [1]) (const nat [])) (app (app (app (app (app (app (const a_dummy.map []) (var 4)) (var 5)) (app (app (app (const lol []) (var 5)) (var 4)) (var 3))) (var 2)) (var 1)) (var 0)))

--(app (app (const rfl [1]) (const rfl [])) (app (app (app (app (app (app (const a_dummy.map []) (var 4)) (var 5)) (app (app (app (const lol []) (var 5)) (var 4)) (var 3))) (var 2)) (var 1)) (var 0)))



-- Π (E F : Type) [_inst_1 : has_lt ℕ] (X Y : Type) (f : F → X → Y), eq ℕ (a_dummy.map (lol E F) f) 42
-- λ (E F : Type) [_inst_1 : has_lt ℕ] (X Y : Type) (f : F → X → Y), rfl

-- ∀ (E F : Type) [_inst_1 : has_lt ℕ] {X Y : Type} (f : F → X → Y), a_dummy.map (lol E F) f = 42
-- λ (E F : Type) [_inst_1 : has_lt ℕ] {X Y : Type} (f : F → X → Y), rfl

#check a_dummy.map

run_cmd do
  e ← tactic.get_env,
  match e.get `lol_map2 with
  | exception _ f := tactic.fail (f options.mk)
  | success decl :=
    match decl with
    | thm  n us type val     := do
      tactic.trace type,
      tactic.trace val.get,
      tactic.trace "",
      tactic.trace us,
      (params, core) ← pure $ strip_lam_binders val.get,
      tactic.trace $ params.map styleize_variable,
      tactic.trace "",
      tactic.trace core,
      tactic.trace "\n",
      tactic.trace core.to_raw_fmt,
      tactic.trace ""
    | cnst n us type _     := sorry
    | ax   n us type       := sorry
    | defn n us type val _ _ := do
      tactic.trace val.to_raw_fmt,
      tactic.trace ""
    end
  end

run_cmd do
  e ← tactic.get_env,
  match e.get `y_1 with
  | exception _ f := tactic.fail (f options.mk)
  | success decl :=
    match decl with
    | thm  n us type _     := sorry
    | cnst n us type _     := sorry
    | ax   n us type       := sorry
    | defn n us type val _ _ := do
      tactic.trace val.to_raw_fmt
    end
  end,
  match e.is_projection `y.c with
  | none := tactic.trace "o"
  | some pi := tactic.trace pi.nparams >> tactic.trace pi.idx
  end



-- run_cmd do
--   t ← tactic.infer_type `(lol),
--   tactic.trace t,
--   let t := strip_pi_binders t,
--   a ← t.1.nth 0,
--   b ← t.1.nth 1,
--   c ← t.1.nth 2,
--   -- let t := t.instantiate_var $ expr.const `K [],
--   tactic.trace (t.1.map styleize_variable),
--   tactic.trace (c.2.1.instantiate_vars [expr.const b.1 [], expr.const a.1 []])

gen_rfl_lemma lol map

#check lol_map
From Stdlib Require Import Strings.String Strings.Ascii List Arith.PeanoNat.
Import ListNotations.
From QuickChick Require Import QuickChick Tactics.
Import QcNotation QcDefaultNotation. Open Scope qc_scope.
Require Export ExtLib.Structures.Monads.
Require Import ExtLib.Data.List.
Import MonadNotation.

From SECF Require Import MiniCET Utils.

Derive Show for observation.

#[export] Instance showVal : Show val :=
  {show :=fun v =>
      match v with
      | N n => show n
      | FP l => ("&" ++ show l)%string
      | UV => "UV"%string
      end
  }.

(* Where the heap ends and the stack begins, which is what a failing case
   usually hinges on.  The cell list says nothing on its own: an address only
   means something relative to these two bounds. *)
Definition show_layout (m : mem) : string :=
  ("heap[0.." ++ show m.(heap_length) ++ ") stack[" ++ show (stack_base m)
    ++ ".." ++ show (stack_top m) ++ ")"
   (* The record carries the lengths and the cells separately, so they can
      disagree; when they do, every address in the report is suspect. *)
    ++ (if Nat.eqb (mem_length m) (stack_top m) then ""
        else " (!! " ++ show (mem_length m) ++ " cells, layout broken)"))%string.

(* The layout first, then the cells. *)
#[export] Instance showMem : Show mem :=
  {show := fun m => (show_layout m ++ ": " ++ show m.(memory))%string}.
  
#[export] Instance showBinop : Show binop :=
  {show :=fun op => 
      match op with
      | BinPlus => "+"%string
      | BinMinus => "-"%string  
      | BinMult => "*"%string
      | BinEq => "="%string
      | BinLe => "<="%string
      | BinAnd => "&&"%string
      | BinImpl => "->"%string
      end
  }.

#[export] Instance showExp : Show exp :=
  {show := 
    (let fix showExpRec (e : exp) : string :=
       match e with
       | ANum n => show n
       | AId x => x
       | ABin o e1 e2 => 
           "(" ++ showExpRec e1 ++ " " ++ show o ++ " " ++ showExpRec e2 ++ ")"
       | ACTIf b e1 e2 =>
           "(" ++ showExpRec b ++ " ? " ++ showExpRec e1 ++ " : " ++ showExpRec e2 ++ ")"
       | FPtr l => "&" ++ show l
       end
     in showExpRec)%string
  }.

#[export] Instance showInst : Show inst :=
  {show := 
      (fun i =>
         match i with
         | ISkip => "skip"
         | IAsgn x e => x ++ " := " ++ show e
         | IDiv x e1 e2 => x ++ " <- div " ++ show e1 ++ ", " ++ show e2
         | IBranch e l => "branch " ++ show e ++ " to " ++ show l
         | IJump l => "jump " ++ show l
         | ILoad x a => x ++ " <- load[" ++ show a ++ "]"
         | IStore a e => "store[" ++ show a ++ "] <- " ++ show e
         | ICall e => "call " ++ show e
         | ICTarget => "ctarget"
         (*| IPeek x => x ++ " <- peek"*)
         | IRet => "ret"
         end)%string
  }.

Derive Show for ty.

(* One instruction per line, each with the [cptr] that addresses it, and an
   arrow on [mark] if it is given.  Hardening expands one source instruction
   into several, so the instruction a failure names is buried at an offset
   nobody can count by hand off a flat block listing. *)
Definition show_prog_marked (mark : option cptr) (p : prog) : string :=
  let show_blk (l : nat) (blk : list inst) : string :=
    fold_left (fun (acc : string) (oi : nat * inst) =>
      let '(o, i) := oi in
      (acc ++ (match mark with
               | Some (l', o') => if andb (Nat.eqb l l') (Nat.eqb o o') then "->" else "  "
               | None => "  "
               end)
           ++ " (" ++ show l ++ ", " ++ show o ++ ")  " ++ show i ++ nl)%string)
      (add_index blk) ""%string in
  (nl ++ fold_left (fun (acc : string) (lb : nat * (list inst * bool)) =>
      let '(l, (blk, callable)) := lb in
      (acc ++ "block " ++ show l ++ (if callable then " (callable)" else "")
           ++ ":" ++ nl ++ show_blk l blk)%string)
     (add_index p) ""%string)%string.

#[export] Instance showProg : Show prog :=
  {show p := show_prog_marked None p}.

(* ################################################################# *)
(** * Failure reports *)

(* When a property fails QuickChick prints the generated inputs, but what
   explains the failure is almost always derived from them: the hardened
   program, the directives that were taken, the trace each semantics produced,
   the slot [sp] points at.  The combinators below give every test the same
   shape for that -- a headline, then labelled values -- so a report from one
   test reads like a report from the next. *)

Definition nl_ascii : ascii := Ascii.ascii_of_nat 10.

Fixpoint indent_aux (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if Ascii.eqb c nl_ascii
      then String c (String " "%char (String " "%char (indent_aux rest)))
      else String c (indent_aux rest)
  end.

(* Two spaces in front of every line, so a multi-line value keeps its own
   layout under its label instead of running into it. *)
Definition indent (s : string) : string := ("  " ++ indent_aux s)%string.

Fixpoint has_nl (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c rest => if Ascii.eqb c nl_ascii then true else has_nl rest
  end.

(* A short value sits next to its label; anything spanning lines gets its own
   indented block. *)
Definition field (label body : string) : string :=
  if has_nl body then (label ++ ":" ++ nl ++ indent body)%string
  else (label ++ ": " ++ body)%string.

Definition fields (fs : list (string * string)) : string :=
  fold_left (fun acc '(l, b) => (acc ++ field l b ++ nl)%string) fs ""%string.

(* A titled block of labelled values: the background a test prints under every
   failure, say. *)
Definition section (title : string) (fs : list (string * string)) : string :=
  (nl ++ title ++ nl ++ fields fs)%string.

(* What a failing test hands to [whenFail]: one line saying what went wrong,
   then the values that explain it. *)
Definition report (headline : string) (fs : list (string * string)) : string :=
  section ("*** " ++ headline)%string fs.

(* Most entries in a report are just a label and the [show] of a value. *)
Definition item {A : Type} `{Show A} (label : string) (a : A) : string * string :=
  (label, show a).

(* ----------------------------------------------------------------- *)
(** ** Program positions *)

(* A failing [forAll] already prints the program it generated, and the guarded
   and hardened programs are deterministic functions of it, so printing one in
   a report mostly buries the line that explains the failure.  Set this to
   [true] while reading a report without the generator's output at hand. *)
Definition print_programs : bool := false.

(* A [cptr] on its own is two numbers; what you want to know is which
   instruction sits there. *)
Definition show_pc (p : prog) (pc : cptr) : string :=
  (show pc ++ match fetch p pc with
              | Some i => "  [" ++ show i ++ "]"
              | None => "  [no instruction -- outside the program]"
              end)%string.

Definition pc_item (label : string) (p : prog) (pc : cptr) : string * string :=
  (label, show_pc p pc).

(* Where [pc] is abstract -- inside the semantics functor -- the instruction is
   as much of the position as a report can carry. *)
Definition inst_item (label : string) (i : option inst) : string * string :=
  (label, match i with
          | Some i => show i
          | None => "<no instruction -- outside the program>"%string
          end).

(* The whole program, with an arrow on [mark] if one is given, but only when
   [print_programs] says so. *)
Definition prog_item (label : string) (mark : option cptr) (p : prog)
  : string * string :=
  (label, if print_programs then show_prog_marked mark p
          else (show (List.length p)
                ++ " blocks (set Printing.print_programs to list them)")%string).

(* The word, without the configuration: a report names the configuration under
   its own label. *)
Definition show_outcome {A : Type} (s : state A) : string :=
  match s with
  | S_Running _ => "running"%string
  | S_Undef => "undefined"%string
  | S_Fault => "fault"%string
  | S_Term => "terminated"%string
  end.

(* ----------------------------------------------------------------- *)
(** ** Directives *)

(* Each semantics functor re-exports [direction] under the name [dir], so the
   [Show] instance has to be declared where the functor is applied; the
   function behind it belongs here. *)
Definition show_direction (d : direction) : string :=
  match d with
  | DBranch b => ("DBranch " ++ show b)%string
  | DCall l => ("DCall " ++ show l)%string
  | DRet l => ("DRet " ++ show l)%string
  end.

(* An empty list of directives means "this step needed no attacker input",
   which is worth saying rather than printing "[]". *)
Definition show_dirs (ds : dirs) : string :=
  match ds with
  | [] => "<none>"%string
  | _ => fold_left (fun acc d =>
            (acc ++ (if String.eqb acc ""%string then ""%string else ", "%string)
                 ++ show_direction d)%string) ds ""%string
  end.

Definition dirs_item (label : string) (ds : dirs) : string * string :=
  (label, show_dirs ds).

(* ----------------------------------------------------------------- *)
(** ** Observations *)

Definition show_obs (o : obs) : string :=
  match o with
  | [] => "<no observations>"%string
  | _ => show o
  end.

(* Where two traces stop agreeing.  [obs_eqb] only says that they differ, and
   on a long trace that leaves the reader to diff it by eye. *)
Fixpoint obs_diff (o1 o2 : obs) : option (nat * string) :=
  match o1, o2 with
  | [], [] => None
  | [], y :: _ => Some (0, ("<trace ended> vs " ++ show y)%string)
  | x :: _, [] => Some (0, (show x ++ " vs <trace ended>")%string)
  | x :: xs, y :: ys =>
      if observation_eqb x y
      then option_map (fun '(i, d) => (S i, d)) (obs_diff xs ys)
      else Some (0, (show x ++ " vs " ++ show y)%string)
  end.

(* Where they part company, on its own: for the reports whose traces are
   already on the screen. *)
Definition obs_diff_item (o1 o2 : obs) : string * string :=
  ("first difference"%string,
    match obs_diff o1 o2 with
    | None => "none -- the traces agree"%string
    | Some (i, d) => ("at index " ++ show i ++ ": " ++ d)%string
    end).

(* The two traces and the first place they part company. *)
Definition obs_items (l1 : string) (o1 : obs) (l2 : string) (o2 : obs)
  : list (string * string) :=
  [ (l1, show_obs o1); (l2, show_obs o2); obs_diff_item o1 o2 ].

(* ----------------------------------------------------------------- *)
(** ** Memory and the call stack *)

(* [sp] against the layout: an [sp] outside the stack, or one that is not an
   address at all, explains most [call] and [ret] failures outright. *)
Definition show_sp (sp_val : val) (m : mem) : string :=
  match sp_val with
  | N n =>
      (show n ++ (if Nat.ltb n (stack_base m)
                  then "  (below the stack base " ++ show (stack_base m) ++ ")"
                  else if Nat.leb (stack_top m) n
                  then "  (at or above the stack top " ++ show (stack_top m) ++ ")"
                  else ""))%string
  | v => (show v ++ "  (not an address)")%string
  end.

(* The live part of the stack, one slot per line with its absolute address and
   a marker on the slot [sp] points at.  Tests allocate far more stack than
   they use, so printing all of it buries the handful of cells that matter:
   everything up to [sp], plus every slot that was ever written, is enough. *)
Definition show_stack (m : mem) (sp_val : val) : string :=
  let base := stack_base m in
  let cells := firstn m.(stack_length) (skipn base m.(memory)) in
  let written := fold_left (fun acc '(i, v) =>
      match v with UV => acc | _ => Nat.max acc (S i) end) (add_index cells) 0 in
  let upto := Nat.max written
                (match sp_val with N n => S (n - base) | _ => 0 end) in
  match firstn upto cells with
  | [] => "<empty>"%string
  | shown =>
      (nl ++ fold_left (fun acc '(i, v) =>
          (acc ++ (if (match sp_val with
                       | N n => Nat.eqb n (base + i)
                       | _ => false
                       end) then "->" else "  ")
               ++ " [" ++ show (base + i) ++ "] " ++ show v ++ nl)%string)
         (add_index shown) ""%string)%string
  end.

(* Printing.v stays a leaf module, so it carries its own cell equality rather
   than importing [Generation.val_eqb]. *)
Definition cell_eqb (v1 v2 : val) : bool :=
  match v1, v2 with
  | N a, N b => Nat.eqb a b
  | FP (a, b), FP (c, d) => andb (Nat.eqb a c) (Nat.eqb b d)
  | UV, UV => true
  | _, _ => false
  end.

(* The addresses at which two memories differ, with both cells.  When two runs
   are supposed to agree, one wrong slot is the usual story, and diffing two
   thousand-cell dumps by eye is hopeless. *)
Definition mem_diff (m1 m2 : mem) : string :=
  let differing :=
    fold_left (fun (acc : string) (iv : nat * (val * val)) =>
      let '(i, (v1, v2)) := iv in
      if cell_eqb v1 v2 then acc
      else (acc ++ "  [" ++ show i ++ "] " ++ show v1 ++ " vs " ++ show v2 ++ nl)%string)
      (add_index (List.combine m1.(memory) m2.(memory))) ""%string in
  ((if Nat.eqb (mem_length m1) (mem_length m2) then ""%string
    else ("  lengths differ: " ++ show (mem_length m1) ++ " vs "
          ++ show (mem_length m2) ++ nl)%string)
   ++ (if String.eqb differing ""%string
       then "  (the cells agree)"%string else differing))%string.

(* What a memory failure needs: the bounds, where [sp] sits in them, the heap
   cells and the part of the stack that was used. *)
Definition mem_items (m : mem) (sp_val : val) : list (string * string) :=
  [ ("memory"%string, show_layout m)
  ; ("sp"%string, show_sp sp_val m)
  ; ("heap"%string, show (firstn m.(heap_length) m.(memory)))
  ; ("stack"%string, show_stack m sp_val) ].

(* ----------------------------------------------------------------- *)
(** ** Configurations *)

(* [cfg] is defined inside the semantics functor, so these take the components
   rather than the configuration itself; instantiate [show_cfg] as the
   [Show cfg] instance wherever the functor is applied.  [sp_val] comes in
   separately because looking a register up needs the functor's map. *)
Definition show_cfg {R : Type} `{Show R} (pc : cptr) (rs : R) (m : mem) : string :=
  fields [item "pc"%string pc; item "reg"%string rs; item "mem"%string m].

(* Everything about a configuration a failing test wants: where it is, what
   sits there, what the registers hold and what the stack looks like. *)
Definition cfg_items {R : Type} `{Show R}
  (p : prog) (pc : cptr) (rs : R) (m : mem) (sp_val : val) : list (string * string) :=
  (pc_item "pc"%string p pc) :: (item "registers"%string rs) :: mem_items m sp_val.

(* A whole configuration as one block, for reports that show two of them side
   by side.  The shapes are spelled out rather than named, because [cfg] and
   its speculative and ideal forms are only named inside the functor. *)
Definition show_ideal_cfg {R : Type} `{Show R}
  (p : prog) (ic : ((cptr * R) * mem) * bool) (sp_val : val) : string :=
  let '(pc, rs, m, ms) := ic in
  fields (cfg_items p pc rs m sp_val ++ [("mis-speculating"%string, show ms)]).

Definition show_spec_cfg {R : Type} `{Show R}
  (p : prog) (sc : (((cptr * R) * mem) * bool) * bool) (sp_val : val) : string :=
  let '(pc, rs, m, ct, ms) := sc in
  fields (cfg_items p pc rs m sp_val
          ++ [("awaiting ctarget"%string, show ct); ("mis-speculating"%string, show ms)]).

(* ----------------------------------------------------------------- *)
(** ** Comparing two runs *)

(* Two semantics end their step in states over different configuration types,
   and only the outcome is being compared, so it is compared by name. *)
Definition outcome_eqb {A B : Type} (s1 : state A) (s2 : state B) : bool :=
  String.eqb (show_outcome s1) (show_outcome s2).

(* The shape every "these two runs must agree" property wants: the same
   outcome, and the same trace.  [fs] carries whatever identifies the runs. *)
Definition check_same_outcome {A B : Type} (headline : string)
  (fs : list (string * string))
  (l1 : string) (s1 : state A) (o1 : obs)
  (l2 : string) (s2 : state B) (o2 : obs) : Checker :=
  printTestCase
    (report headline
       (fs ++ [ ((l1 ++ " outcome")%string, show_outcome s1)
              ; ((l2 ++ " outcome")%string, show_outcome s2) ]
           ++ obs_items (l1 ++ " trace")%string o1 (l2 ++ " trace")%string o2))
    (checker (andb (outcome_eqb s1 s2) (obs_eqb o1 o2))).

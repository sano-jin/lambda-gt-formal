section\<open>Introduction\<close>

text \<open>
This is a proof for the soundness of the type system of the $\lambda_{GT}$ language.
\<close>


theory LambdaGT_Core
imports
  Main
  "HOL-Library.Multiset"
begin

declare [[syntax_ambiguity_warning = false]]
declare [[smt_oracle = false]]


section\<open>Syntax, Semantics and Type System of the Language\<close>

subsection \<open>Syntax of the Language\<close>

type_synonym link = nat
type_synonym links = "link list"
text \<open>
We use natural numbers as link identifiers.
A value of type \<^typ>\<open>link\<close> represents a single link name,
and a value of type \<^typ>\<open>links\<close> represents a finite list of such names.
Links are handled using de Bruijn indices: the number \<open>0\<close> refers to the
innermost bound link, \<open>1\<close> to the next one, and so on.
\<close>


datatype 'ty graph =
    Zero
  | Atom "'ty p" links
  | Fusion link link
  | Mol "'ty graph" "'ty graph"
  | Nu "'ty graph"
and 'ty exp =
    Graph "'ty graph"
  | App "'ty exp" "'ty exp" (infixl \<open>\<cdot>\<close> 200)
  | Case  "'ty exp" "(links * 'ty) list" "'ty graph" "'ty exp" "'ty exp"
and 'ty p =
    GConstr string
  | GVar nat
  | GAbs links 'ty "'ty exp"
text \<open>
The syntax of HyperLMNtal graphs, expressions, and atomic patterns is
given by the following mutually recursive datatypes.

\<^item> \<^typ>\<open>'ty graph\<close> is the type of graphs, parameterised by a type annotation
      \<^typ>\<open>'ty\<close>.
  \<^item> \<open>Zero\<close> is the empty graph.
  \<^item> \<open>Atom p xs\<close> is an atomic cell with principal atom \<open>p\<close> and a list
        \<open>xs\<close> of incident links.
  \<^item> \<open>Fusion x y\<close> represents a fusion (equality) constraint between links
        \<open>x\<close> and \<open>y\<close>.
  \<^item> \<open>Mol g1 g2\<close> is the parallel composition (multiset union) of graphs
        \<open>g1\<close> and \<open>g2\<close>.
  \<^item> \<open>Nu g\<close> introduces a fresh link scope around \<open>g\<close>.  The binder
        \<open>Nu\<close> binds link index \<open>0\<close> in \<open>g\<close>; all other free link
        indices in \<open>g\<close> are shifted accordingly.

\<^item> \<^typ>\<open>'ty exp\<close> is the type of expressions over graphs.
  \<^item> \<open>Graph g\<close> embeds a graph \<open>g\<close> as a trivial expression.
  \<^item> \<open>App e1 e2\<close> (written \<open>e1 \<cdot> e2\<close>) is application of \<open>e1\<close> to \<open>e2\<close>.
  \<^item> \<open>Case e \<Gamma> T e1 e2\<close> is a case expression:
        it inspects the value of \<open>e\<close>, tries to match it against the
        graph pattern \<open>T\<close> using the rule environment \<open>\<Gamma>\<close>, and
        continues with \<open>e1\<close> on success or \<open>e2\<close> on failure.

\<^item> \<^typ>\<open>'ty p\<close> is the type of principal atoms.
  \<^item> \<open>GConstr s\<close> is a constructor with name \<open>s\<close>.
  \<^item> \<open>GVar i\<close> is a de Bruijn index \<open>i\<close> for an expression variable.
  \<^item> \<open>GAbs xs ty e\<close> is an abstraction whose body is \<open>e\<close>, with a list
        of interface links \<open>xs\<close> and a type annotation \<open>ty\<close>.  The bound
        variable is represented by index \<open>0\<close> in \<open>e\<close>, and outer variables
        are shifted as usual for de Bruijn indices.
\<close>


text \<open>
Free links of graphs.
The constructor Nu binds the link index 0 in its subgraph,
and all other free links are shifted down by one.
\<close>
primrec FL :: "'ty graph => link set"
where
  "FL Zero = {}"
| "FL (Atom p links) = set links"
| "FL (Fusion x y) = {x, y}"
| "FL (Mol g1 g2) = FL g1 \<union> FL g2"
| "FL (Nu g) = {n. Suc n \<in> FL g}"


lemma shift_down_alt:
  "{n. Suc n \<in> S} = (\<lambda>x. x - 1) ` (S - {0})"
apply auto
by (metis Zero_not_Suc diff_Suc_1' imageI insert_Diff_single insert_iff)



subsection \<open>Link Substitution\<close>

text \<open>Link Substitution Over Graphs\<close>

text \<open>
Free link substitution.
Note that this is design not to change any local links.
\<close>
primrec
  lmap :: "(link => link) => 'ty graph => 'ty graph"
where
    "lmap f Zero = Zero"
 |  "lmap f (Atom p xs) = Atom p (map f xs)"
 |  "lmap f (Fusion  x y) = Fusion (f x) (f y)"
 |  "lmap f (Mol g1 g2) = Mol (lmap f g1) (lmap f g2)"
 |  "lmap f (Nu g) = Nu (lmap (\<lambda>x. if x = 0 then x else (f (x - 1) + 1)) g)"


lemma succ_after_before:
  "{n. Suc n \<in> (\<lambda>x. if x = 0 then x else (f (x - 1) + 1)) ` S} =
   f ` {n. Suc n \<in> S}"
apply auto
by force


text \<open>Simultaneous Link Substitution\<close>


text \<open>
Definition of Simultaneous Link Substitution.
\<close>
fun lsubst :: "(link * link) list => link => link" where
  "lsubst [] x = x" |
  "lsubst ((v, n) # s) x = (if x = v then n else lsubst s x)"


lemma lsubst_simp:
  "lsubst (vn # s) x = (if x = fst vn then snd vn else lsubst s x)"
by (metis lsubst.simps(2) prod.collapse)


subsection \<open>Congruence Relation\<close>


text \<open>
  We first define the congruence relatin over graphs
  and prove some properties of the relation.
\<close>

text \<open>
  Inductive definition of graph equivalence.
\<close>
inductive gcong :: "'ty graph => 'ty graph => bool" (infix "\<simeq>" 50)
where
 (* Equivalence-closure: *)
  refl [intro!]: "g \<simeq> g"
| sym  [intro]:  "g1 \<simeq> g2 ==> g2 \<simeq> g1"
| trans[trans]:  "g1 \<simeq> g2 ==> g2 \<simeq> g3 ==> g1 \<simeq> g3"

 (* Algebraic laws: E1, E2, E3. *)
| mol_zero [simp]: "Mol g Zero \<simeq> g"
| mol_comm [simp]: "Mol g1 g2 \<simeq> Mol g2 g1"
| mol_assoc[simp]: "Mol (Mol a b) c \<simeq> Mol a (Mol b c)"

 (* Congruence/compatibility (so rules lift through contexts): E4, E5 *)
| mol_cong[intro]: "g1 \<simeq> g1' ==> g2 \<simeq> g2' ==> Mol g1 g2 \<simeq> Mol g1' g2'"
| nu_cong [intro]: "g \<simeq> g' ==> Nu g \<simeq> Nu g'"

(* Hyperlink hiding: E6, E7, E8, E9, E10 *)
(* E6 *)
| nu_subst_fusion1:
  "y \<in> FL g ==> Nu (Mol (Fusion 0 y) g) \<simeq> Nu (lmap (\<lambda>x. if x = 0 then y else x) g)"
| nu_subst_fusion2:
  "0 \<in> FL g ==> Nu (Mol (Fusion 0 y) g) \<simeq> Nu (lmap (\<lambda>x. if x = 0 then y else x) g)"

(* E7 *)
| nu_nu_fusion1 [simp]: "Nu (Nu (Fusion 0 1)) \<simeq> Zero"
| nu_nu_fusion2 [simp]: "Nu (Fusion 0 0) \<simeq> Zero"

(* E8 *)
| nu_zero [simp]: "Nu Zero \<simeq> Zero"

(* E9 *)
| nu_comm: "Nu (Nu g) \<simeq> Nu (Nu (lmap (\<lambda>x. if x = 0 then 1 else if x = 1 then x else x) g))"

(* E10 *)
| nu_scope: "Mol (Nu g1) g2 \<simeq> Nu (Mol g1 (lmap Suc g2))"


text \<open>
Some helper functions for building a graph.
\<close>

definition Mols1:
  "Mols1 g gs = foldl Mol g gs"

primrec Nus1 :: "nat => 'ty graph => 'ty graph" where
  "Nus1 0 g = g"
| "Nus1 (Suc n) g = Nu (Nus1 n g)"


subsection \<open>Variable Lift and Graph Substitution\<close>

text \<open>
  The lifting operation @{term "lift t k"} shifts free de Bruijn indices
  stored in @{const GVar} that are greater than by 1.
  When we go under an @{const GAbs} binder, we increase the cutoff to @{term "k + 1"}.
  Graph-level binders @{const Nu} bind links, not expression variables,
  so they do not affect the cutoff for lifting expression variables.
\<close>

primrec lift :: "nat => 'ty exp => 'ty exp"
and lift_atom :: "nat => 'ty p => 'ty p"
and lift_graph :: "nat => 'ty graph => 'ty graph"
where
  (* exp cases *)
  "lift k (Graph g) = Graph (lift_graph k g)"
| "lift k (App e1 e2) = App (lift k e1) (lift k e2)"
| "lift k (Case e \<Gamma> T e1 e2) =
       Case (lift k e) \<Gamma> T (lift (k + length \<Gamma>) e1) (lift k e2)"

  (* atom_name cases *)
| "lift_atom k (GConstr s) = GConstr s"
| "lift_atom k (GVar i) =
       (if i < k then GVar i else GVar (i + 1))"
| "lift_atom k (GAbs \<tau> xs e) =
       GAbs \<tau> xs (lift (k + 1) e)"

  (* graph cases *)
| "lift_graph k Zero = Zero"
| "lift_graph k (Atom a vs) = Atom (lift_atom k a) vs"
| "lift_graph k (Fusion x y) = Fusion x y"
| "lift_graph k (Mol g1 g2) =
       Mol (lift_graph k g1) (lift_graph k g2)"
| "lift_graph k (Nu g) =
       Nu (lift_graph k g)"


text \<open>
  Capture-avoiding substitution @{term "e'[e/i]"} on expressions, atoms, and graphs.
  This is a structural skeleton; the behavior on variable occurrences (GVar)
  must be decided to make this a real substitution.
\<close>
primrec subst :: "nat => links => 'ty graph => 'ty exp => 'ty exp"
and subst_graph :: "nat => links => 'ty graph => 'ty graph => 'ty graph"
and subst_p :: "nat => links => 'ty graph => 'ty p => links => 'ty graph"
where
  (* exp cases *)
  "subst i xs G (Graph g) = Graph (subst_graph i xs G g)"
| "subst i xs G (App e1 e2) = App (subst i xs G e1) (subst i xs G e2)"
| "subst i xs G (Case e0 \<Gamma> T e1 e2) =
       Case (subst i xs G e0) \<Gamma> T
            (subst (i + length \<Gamma>) xs ((lift_graph 0 ^^ (length \<Gamma>)) G) e1)
	    (subst i xs G e2)"

  (* p cases *)
| "subst_p i xs G (GConstr s) ys = Atom (GConstr s) ys"
| "subst_p i xs G (GAbs zs ty e0) ys =
     Atom (GAbs zs ty (subst (i + 1) xs (lift_graph 0 G) e0)) ys"
| "subst_p i xs G (GVar j) ys =
      (if i < j then (Atom (GVar (j - 1)) ys)
       else if j = i \<and> length xs = length ys then lmap (lsubst (zip xs ys)) G
       else (Atom (GVar j) ys))"

  (* graph cases *)
| "subst_graph i xs G Zero = Zero"
| "subst_graph i xs G (Atom p ys) = subst_p i xs G p ys "
| "subst_graph i xs G (Fusion x y) = Fusion x y"
| "subst_graph i xs G (Mol g1 g2) = Mol (subst_graph i xs G g1) (subst_graph i xs G g2)"
| "subst_graph i xs G (Nu g) = Nu (subst_graph i xs G g)"


definition substs_graph:
  "substs_graph XsGs T = fold (\<lambda> ((xs, _), g). subst_graph 0 xs g) XsGs T"

definition substs:
  "substs XsGs e = fold (\<lambda> ((xs, _), g). subst 0 xs g) XsGs e"

(* Must holds: set xs = FL Gs. *)


(* Prefer these simp facts to normalize conditionals/inequalities in goals. *)
declare if_not_P [simp] not_less_eq [simp]
  \<comment> \<open>don't add \<open>r_into_rtrancl[intro!]\<close>\<close>


subsection \<open>Value\<close>


text \<open>
Values are exactly abstractions and base-type literals.
\<close>
primrec is_atom_val :: "'ty p => bool" where
  "is_atom_val (GConstr s) = True"
| "is_atom_val (GAbs xs ty e) = True"
| "is_atom_val (GVar i) = False"


text \<open>
Values are exactly abstractions and base-type literals.
\<close>
primrec is_graph_val :: "'ty graph => bool" where
  "is_graph_val Zero = True"
| "is_graph_val (Atom p xs) = is_atom_val p"
| "is_graph_val (Fusion x y) = True"
| "is_graph_val (Mol g1 g2) = (is_graph_val g1 \<and> is_graph_val g2)"
| "is_graph_val (Nu g) = is_graph_val g"



lemma is_graph_val_ignore_lmap:
  "is_graph_val (lmap f g) = is_graph_val g"
apply (induct g arbitrary: f rule: graph.induct[of _ "%_. True" "%_. True"])
by auto


lemma cong_is_graph_val:
  assumes "g1 \<simeq> g2"
  shows "is_graph_val g1 = is_graph_val g2"
using assms
apply (induct set: gcong)
apply (simp_all add: is_graph_val_ignore_lmap)
by auto


text \<open>
Values are exactly abstractions and base-type literals.
\<close>
primrec is_val :: "'ty exp => bool" where
  "is_val (Graph g) = is_graph_val g"
| "is_val (App e1 e2) = False"
| "is_val (Case e0 \<Gamma> T e1 e2) = False"


lemma cong_is_val:
  assumes "g1 \<simeq> g2"
  shows "is_val (Graph g1) = is_val (Graph g2)"
using assms
by (simp add: cong_is_graph_val)



subsection \<open>Type System\<close>


text \<open>
  We first define environments and then define typing relations.
\<close>


text \<open>Environments\<close>


text \<open>
  Environments are represented as lists, where the head corresponds to the
  most recently inserted binding (de Bruijn-style contexts).
\<close>
type_synonym ('a) env = "'a list"


text \<open>
  @{term "insert_at xs j x"} inserts element x at position j in xs.
\<close>
fun insert_at :: "'a env => nat => 'a => 'a env" where
  "insert_at xs       0       x = x # xs" |
  "insert_at []       (Suc n) x = [x]" |
  "insert_at (y # ys) (Suc n) x = y # insert_at ys n x"


text \<open>Types and Typing Rules\<close>


text \<open>
  Simple types:
  \<^item> \<open>TBase n xs\<close> : base type identified by \<open>n\<close> with free links \<open>xs\<close>
  \<^item> \<open>TArrow ty1 ty2 xs\<close> : function type \<open>ty1 => ty2\<close> with free links \<open>xs\<close>.
\<close>
datatype type =
    TBase nat links
  | TArrow type type links

text \<open>
  Typing environments map de Bruijn indices to (links, type) pairs.
  The head is the most recently bound variable.
\<close>
type_synonym tyenv = "(links * type) list"

text \<open>Right-hand side of a production rule.\<close>
type_synonym prodrule_RHS =
  "nat * (string * links) * (link * link) list * type list"

text \<open>Whole production rule: left-hand side tag / links and RHS.\<close>
type_synonym prodrule =
  "(nat * links) * prodrule_RHS"


primrec FLty :: "type => link set" where
  "FLty (TBase i xs) = set xs"
| "FLty (TArrow ty1 ty2 xs) = set xs"


text \<open>
  Free links of a RHS: we shift by \<open>i\<close> to account for the \<open>Nus1 i\<close> binder.
\<close>
definition FLrhs :: "prodrule_RHS => link set" where
  "FLrhs rhs \<equiv>
   (case rhs of (i, (C, zs), fusions, taus) =>
      {n. n + i \<in>
            ( set zs
            \<union> (\<Union>(x, y)\<in>set fusions. {x, y})
            \<union> (\<Union> (FLty ` set taus)))})"


text \<open>
  Free-link substitution on types.
\<close>
primrec lmap_ty :: "links => links => type => type" where
  "lmap_ty xs ys (TBase i zs) =
     TBase i (map (lsubst (zip xs ys)) zs)"
| "lmap_ty xs ys (TArrow ty1 ty2 zs) =
     TArrow ty1 ty2 (map (lsubst (zip xs ys)) zs)"



text \<open>
  Turn a list of link pairs \<open>(x, y)\<close> into a list of fusion graphs \<open>Fusion x y\<close>.
\<close>
definition fusions_of :: "(link * link) list => type graph list" where
  "fusions_of fusions = map (\<lambda>(x, y). Fusion x y) fusions"

definition taus_of_rhs :: "prodrule_RHS => type list" where
  "taus_of_rhs rhs =
     (case rhs of (i, (C, zs), fusions, taus) => taus)"


text \<open>
  Apply a production rule to argument graphs \<open>Ts\<close>.
\<close>
definition app_prodrule ::
  "type graph list => prodrule_RHS => type graph" where
  "app_prodrule Ts rhs =
     (case rhs of (i, (C, zs), fusions, taus) =>
        Nus1 i (Mols1 (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) Ts))"


text \<open>
Typing rules.
\<close>
inductive typing ::
  "tyenv => prodrule list => type exp => type => bool"
  (\<open>_ \<turnstile>{_} _ : _\<close> [50, 50, 50, 50] 50)
where
  TyVar:
    "i < length \<Gamma> ==>
     \<Gamma> ! i = (xs, ty) ==>
     length xs = length ys ==>
     distinct xs ==>
     distinct ys ==>
     set xs = FLty ty ==>
     \<Gamma> \<turnstile>{P} Graph (Atom (GVar i) ys) : lmap_ty xs ys ty"
| TyArrow:
    "(xs, ty1) # \<Gamma> \<turnstile>{P} e : ty2 ==>
     distinct xs ==>
     set xs = FLty ty1 ==>
     \<Gamma> \<turnstile>{P} Graph (Atom (GAbs xs ty1 e) ys) : TArrow ty1 ty2 ys"
| TyApp:
    "\<Gamma> \<turnstile>{P} e1 : TArrow ty1 ty2 xs ==>
     \<Gamma> \<turnstile>{P} e2 : ty1 ==>
     \<Gamma> \<turnstile>{P} e1 \<cdot> e2 : ty2"
| TyProd:
    "((a, xs), rhs) \<in> set P ==>
     taus = taus_of_rhs rhs ==>
     length taus = length Ts ==>
     (\<forall>i < length Ts. \<Gamma> \<turnstile>{P} (Graph (Ts ! i)) : taus ! i) ==>
     set xs = FLrhs rhs ==>
     \<Gamma> \<turnstile>{P} (Graph (app_prodrule Ts rhs)) : TBase a xs"
| TyCong:
    "\<Gamma> \<turnstile>{P} Graph g1 : ty ==>
     g1 \<simeq> g2 ==>
     \<Gamma> \<turnstile>{P} Graph g2 : ty"
| TyAlpha:
    "\<Gamma>2 \<turnstile>{P} Graph g : ty ==>
     set xs = FL g ==>
     length xs = length ys ==>
     distinct xs ==>
     distinct ys ==>
     \<Gamma>2 \<turnstile>{P} Graph (lmap (lsubst (zip xs ys)) g)
         : lmap_ty xs ys ty"
| TyCase:
    "\<Gamma> \<turnstile>{P} e0 : ty1 ==>
     \<Gamma>2 @ \<Gamma> \<turnstile>{P} e1 : ty2 ==>
     \<Gamma> \<turnstile>{P} e2 : ty2 ==>
     \<Gamma> \<turnstile>{P} Case e0 \<Gamma>2 T e1 e2 : ty2"


text \<open>
  Inversion rules for the typing judgment.
  They let us analyse typing derivations for particular syntactic forms.
\<close>

inductive_cases typing_GVarE [elim!]:
  "\<Gamma> \<turnstile>{P} Graph (Atom (GVar i) ys) : ty"

inductive_cases typing_GAbsE [elim!]:
  "\<Gamma> \<turnstile>{P} Graph (Atom (GAbs xs ty1 e) ys) : ty"

inductive_cases typing_AppE [elim!]:
  "\<Gamma> \<turnstile>{P} e1 \<cdot> e2 : ty"

inductive_cases typing_GraphE [elim!]:
  "\<Gamma> \<turnstile>{P} (Graph g) : ty"


subsection\<open>Reduction Relations\<close>



text \<open>
Call-by-value small-step relation on expressions.
- Perform beta only when the argument graph is already a value.
- Case on a value graph that matches the pattern graph.
- Case on a non-graph value (falls through to the else branch).
- Evaluate the function part first (left-to-right).
- Then evaluate the argument, once the function is a value.
No reduction happens inside abstractions.
\<close>
inductive cbv_ty :: "type exp => prodrule list => type exp => bool"
  ("_ ->{_} _" [60,0,61] 60)
where
  beta_v_ty [simp, intro]:
    "is_graph_val v ==> distinct xs ==> FL v = set xs ==>
     lam \<simeq> Atom (GAbs xs ty e) ys ==>
     Graph lam \<cdot> Graph v ->{P} subst 0 xs v e"
| case1_v_ty [simp, intro]:
    "is_graph_val v ==>
     length \<Gamma> = length gs ==>
     XsGs = zip \<Gamma> gs ==>
     v \<simeq> substs_graph XsGs T ==>
     \<forall>((xs, ty), g) \<in> set XsGs. (
       distinct xs \<and> FL g = set xs \<and>
       [] \<turnstile>{P} (Graph g) : ty
     ) ==>
     Case (Graph v) \<Gamma> T e1 e2 ->{P} substs XsGs e1"
| case2_v_ty [simp, intro]:
    "is_graph_val v ==>
     Case (Graph v) \<Gamma> T e1 e2 ->{P} e2"
| appL_ty   [simp, intro]:
    "e1 ->{P} e1' ==>
     e1 \<cdot> e2 ->{P} e1' \<cdot> e2"
| appR_ty   [simp, intro]:
    "is_val v ==>
     e ->{P} e' ==>
     v \<cdot> e ->{P} v \<cdot> e'"
| caseL_ty   [simp, intro]:
    "e0 ->{P} e0' ==>
     Case e0 \<Gamma> T e1 e2 ->{P} Case e0' \<Gamma> T e1 e2"


text \<open>
  Inversion rules for the call-by-value step relation.
\<close>

inductive_cases cbv_ty_AppE [elim!]:
  "e1 \<cdot> e2 ->{P} e"

inductive_cases cbv_ty_CaseE [elim!]:
  "Case e0 \<Gamma> T e1 e2 ->{P} e"

inductive_cases cbv_ty_GraphE [elim!]:
  "Graph g ->{P} e"


text \<open>
  Zero or more reductions.
\<close>
abbreviation cbv_ty_star ::
  "type exp => prodrule list => type exp => bool"
  ("_ ->{_}* _" [60,0,61] 60)
where
  "e ->{P}* e' \<equiv> rtranclp (\<lambda>e e'. cbv_ty e P e') e e'"


section\<open>Congruence Relations\<close>

text \<open>
Show it's an equivalence relation (useful for rewriting/quotients).
\<close>

lemma gcong_reflp: "reflp (\<simeq>)"
  by (simp add: gcong.refl reflpI)

lemma gcong_symp: "symp (\<simeq>)"
  by (simp add: gcong.sym sympI)

lemma gcong_transp: "transp (\<simeq>)"
  using gcong.trans transpI by blast

lemma gcong_equivp: "equivp (\<simeq>)"
  by (simp add: gcong_reflp gcong_symp gcong_transp equivpI)



section\<open>Properties of Link Substitution\<close>

subsection\<open>Basic Properties of Link Substitution\<close>

lemma FL_lmap_commute:
  fixes g :: "'ty graph"
  shows "FL (lmap f g) = f ` (FL g)"
proof (induct g arbitrary: f)
  case (Nu g)
  have "FL (lmap f (Nu g)) = FL (Nu (lmap (\<lambda>x. if x = 0 then x else (f (x - 1) + 1)) g))"
    by simp
  also have "... = {n. Suc n \<in> FL (lmap (\<lambda>x. if x = 0 then x else (f (x - 1) + 1)) g)}"
    by simp
  also have "... = {n. Suc n \<in> (\<lambda>x. if x = 0 then x else (f (x - 1) + 1)) ` FL g}"
      using Nu by blast
  also have "... = f ` {n. Suc n \<in> FL g}"
     using succ_after_before by presburger
  also have "... = f ` FL (Nu g)"
     by simp
  finally show ?case .
qed auto


lemma FL_lmap_deSuc_Suc:
  fixes k n :: nat
    and g :: "'ty graph"
  shows "{n. Suc n \<in> FL (lmap Suc g)} = FL g"
apply (simp add: FL_lmap_commute)
by auto


subsection\<open>Basic Properties of Simultaneous Link Substitution\<close>


lemma lsubst_cdom:
  assumes "x \<in> set (map fst xs)"
  shows "lsubst xs x \<in> set (map snd xs)"
using assms
proof (induct xs)
  case Nil
  then show ?case
  apply auto
  done
next
  case (Cons a xs)
  then show ?case
  apply (cases "x = fst a")
  using lsubst_simp
  by auto
qed


lemma lsubst_image_aux:
  assumes "distinct (map fst s)"
  shows "map (lsubst s) (map fst s) = map snd s"
using assms
proof (induct s)
  case Nil
  then show ?case
  apply auto
  done
next
  case (Cons a s)
  then show ?case
  apply auto
  using lsubst_simp apply presburger
  using lsubst_simp apply auto
  by (metis fstI image_eqI)
qed


lemma lsubst_image:
  assumes "distinct (map fst s)"
  shows "lsubst s ` set (map fst s) = set (map snd s)"
by (metis assms list.set_map lsubst_image_aux)


lemma lsubst_zip_image:
  assumes "length xs = length ys"
  assumes "distinct xs"
  shows "lsubst (zip xs ys) ` set xs = set ys"
using assms
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case
  apply auto
  done
next
  case (Cons a xs)
  then show ?case
  by (metis lsubst_image map_fst_zip map_snd_zip)
qed


subsection\<open>Link Substitution Before/After Inverse Link Substitution\<close>

text \<open>
Swappling links.
\<close>
abbreviation swap_list :: "('a * 'b) list => ('b * 'a) list"
  where "swap_list xs \<equiv> map (\<lambda>(x, y). (y, x)) xs"

lemma swap_swap_list [simp]:
  "swap_list (swap_list xs) = xs"
apply (induct xs)
by auto

lemma swap_map_fst [simp]:
  "map fst (swap_list xs) = map snd xs"
apply (induct xs)
by auto


lemma swap_map_snd [simp]:
  "map snd (swap_list xs) = map fst xs"
apply (induct xs)
by auto


lemma lsubst_inv_cdom:
  assumes "y \<in> set (map snd xs)"
  shows "lsubst (swap_list xs) y \<in> set (map fst xs)"
by (metis assms lsubst_cdom swap_map_fst swap_map_snd)


lemma lsubst_inv_inv:
  assumes "distinct (map fst xs)"
  assumes "y \<in> set (map snd xs)"
  shows "lsubst xs (lsubst (swap_list xs) y) = y"
using assms
proof (induct xs arbitrary: y)
  case Nil
  then show ?case
  apply auto
  done
next
  case (Cons a xs)
  obtain x y' where
    decomp: "(x, y') = a"
  by (metis surj_pair)

  then show ?case
  proof (cases "y = y'")
    case True
    have "lsubst ((x, y') # xs) (lsubst (swap_list ((x, y') # xs)) y) = y"
      by (simp add: True)
    then show ?thesis
      using decomp by fastforce
  next
    case False
    have P0: "y \<in> set (map snd xs)"
      using Cons.prems(2) False decomp by fastforce
    then have "lsubst (swap_list xs) y \<in> set (map fst xs)"
      using lsubst_inv_cdom by presburger
    then have P3: "lsubst (swap_list xs) y \<noteq> x"
      using Cons.prems(1) decomp by force

    have "lsubst (a # xs) (lsubst (swap_list (a # xs)) y) =
          lsubst ((x, y') # xs) (lsubst (swap_list ((x, y') # xs)) y)"
      using decomp by simp
    also have "... = lsubst ((x, y') # xs) (lsubst ((y', x) # swap_list xs) y)"
      by simp
    also have "... = lsubst ((x, y') # xs) (lsubst (swap_list xs) y)"
      by (simp add: False)
    also have "... = lsubst xs (lsubst (swap_list xs) y)"
      by (simp add: P3)
    also have "... = y"
      using Cons.hyps Cons.prems(1) P0 by auto
    finally show ?thesis .
  qed
qed


corollary lsubst_inv_inv2:
  assumes "distinct (map snd xs)"
  assumes "y \<in> set (map fst xs)"
  shows "lsubst (swap_list xs) (lsubst xs y) = y"
by (metis assms(1,2) lsubst_inv_inv swap_map_fst swap_swap_list)


lemma map_lsubst_inv_inv:
  assumes "distinct (map fst xs)"
  assumes "set ys \<subseteq> set (map snd xs)"
  shows "map (lsubst xs o lsubst (swap_list xs)) ys = ys"
using assms
proof (induct ys)
  case Nil
  then show ?case
  apply auto
  done
next
  case (Cons a ys)
  then show ?case
  apply auto
  using Cons.prems(2) lsubst_inv_inv by auto
qed


corollary map_lsubst_zip_inv_inv:
  assumes "distinct xs"
  assumes "set ys' \<subseteq> set ys"
  assumes "length xs = length ys"
  shows "map (lsubst (zip xs ys) o lsubst (zip ys xs)) ys' = ys'"
by (metis assms(1,2,3) map_fst_zip map_lsubst_inv_inv map_snd_zip zip_commute)


lemma lmap_lsubst_inv_inv_aux:
  assumes "distinct (map fst xs)"
  assumes "distinct (map snd xs)"
  assumes "\<forall>y \<in> FL g. y >= k --> y - k \<in> set (map fst xs)"
  shows  "lmap (\<lambda>x. if x < k then x else (lsubst (swap_list xs) (x - k) + k))
            (lmap (\<lambda>x. if x < k then x else (lsubst xs (x - k) + k)) g) = g"
using assms
proof (induct g arbitrary: k rule: graph.induct[of _ "%_. True" "%_. True"])
  case Zero
  then show ?case
  apply auto
  done
next
  case (Atom x1 x2)
  then show ?case
  apply auto
  by (simp add: FL.simps(2) comp_apply lsubst_inv_inv2 map_idI)
next
  case (Fusion x1 x2)
  then show ?case
  apply auto
  using lsubst_inv_inv2 apply fastforce
  using lsubst_inv_inv2 apply fastforce
  using lsubst_inv_inv2 apply fastforce
  using lsubst_inv_inv2 apply fastforce
  using lsubst_inv_inv2 apply fastforce
  using lsubst_inv_inv2 apply fastforce
  done
next
  case (Mol x1 x2)
  then show ?case
  apply auto
  done
next
  case (Nu g')
  have "\<forall>y \<in> FL (Nu g'). y >= k --> y - k \<in> set (map fst xs)"
    using Nu.prems(3) by blast
  then have P2: "\<forall>y \<in> FL g'. y >= Suc k --> y - (Suc k) \<in> set (map fst xs)"
    by (metis FL.simps(5) Suc_le_D Suc_le_mono diff_Suc_Suc mem_Collect_eq)

  have P3:
    "(\<lambda>x. if x = 0 then x else (if x - 1 < k then x - 1 else lsubst (swap_list xs) (x - 1 - k) + k) + 1) =
    (\<lambda>x. if x < Suc k then x else lsubst (swap_list xs) (x - (Suc  k)) + (Suc k))"
    using ab_semigroup_add_class.add_ac(1) add.commute diff_diff_eq not0_implies_Suc not_less_eq
      by fastforce

  have P4:
    "(\<lambda>x. if x = 0 then x else (if x - 1 < k then x - 1 else lsubst xs (x - 1 - k) + k) + 1) =
    (\<lambda>x. if x < Suc k then x else lsubst xs (x - (Suc  k)) + (Suc k))"
    using add_cancel_right_right add_diff_inverse_nat diff_Suc_eq_diff_pred less_Suc_eq less_imp_diff_less
      not_less_eq plus_1_eq_Suc by fastforce


   have P5:
 "lmap (\<lambda>x. if x = 0 then x else (if x - 1 < k then x - 1 else lsubst (swap_list xs) (x - 1 - k) + k) + 1)
   (lmap (\<lambda>x. if x = 0 then x else (if x - 1 < k then x - 1 else lsubst xs (x - 1 - k) + k) + 1) g') =
  lmap (\<lambda>x. if x < Suc k then x else lsubst (swap_list xs) (x - (Suc k)) + (Suc k))
   (lmap (\<lambda>x. if x < Suc k then x else lsubst xs (x - (Suc k)) + (Suc k)) g')"
   using P3 P4 by argo

  show ?case
  apply auto
   using Nu.hyps Nu.prems(2) P2 P5 assms(1) by presburger
qed auto


corollary lmap_lsubst_inv_inv:
  assumes "distinct (map fst xs)"
  assumes "distinct (map snd xs)"
  assumes "FL g \<subseteq> set (map fst xs)"
  shows  "lmap (lsubst (swap_list xs)) (lmap (lsubst xs) g) = g"
proof -
  have "\<forall>y \<in> FL g. y >= 0 --> y - 0 \<in> set (map fst xs)"
    apply auto
    using assms(3) by auto
  then have "lmap (\<lambda>x. if x < 0 then x else (lsubst (swap_list xs) (x - 0) + 0))
            (lmap (\<lambda>x. if x < 0 then x else (lsubst xs (x - 0) + 0)) g) = g"
    using assms(1,2) lmap_lsubst_inv_inv_aux by blast
  then show ?thesis
  by simp
qed


subsection\<open>Basic Property of Link Substitution Over Types\<close>


lemma lmap_ty_inv_inv:
  assumes "length xs = length ys"
  assumes "distinct xs"
  assumes "distinct ys"
  assumes "FLty ty \<subseteq> set xs"
  shows  "lmap_ty ys xs (lmap_ty xs ys ty) = ty"
using assms
proof (induct ty)
  case (TBase x1 x2)
  then show ?case
  apply (simp add: lmap_ty_def)
  using map_lsubst_zip_inv_inv by force
next
  case (TArrow ty1 ty2 x3)
  then show ?case
  apply (simp add: lmap_ty_def)
  using map_lsubst_zip_inv_inv by force
qed


text \<open>
Free links of a left-folded \<open>Mol\<close>.
\<close>
lemma FL_Mols1:
  "FL (Mols1 g gs) = FL g \<union> \<Union> (FL ` set gs)"
apply (induct gs arbitrary: g)
apply (simp_all add: Mols1)
by auto


text \<open>
Free links after \<open>i\<close> nested \<open>Nu\<close> binders.
\<close>
lemma FL_Nus1:
  "FL (Nus1 i g) = {n. n + i \<in> FL g}"
  by (induct i arbitrary: g) auto


lemma app_prodrule_FL_equiv:
  assumes A1: "taus = taus_of_rhs rhs"
  assumes A3: "map FLty taus = map FL Ts"
  shows "FL (app_prodrule Ts rhs) = FLrhs rhs"
proof -
  obtain i C zs fusions taus' where
    prod_rhs: "rhs = (i, (C, zs), fusions, taus')"
   by (metis prod.collapse)

  have taus: "taus' = taus"
    by (simp add: A1 prod_rhs taus_of_rhs_def)
  then have prod_rhs2: "rhs = (i, (C, zs), fusions, taus)"
    by (simp add: prod_rhs)


  have FL_fusions:
    "\<Union> (FL ` set (fusions_of fusions)) = (\<Union> (x, y) \<in> set fusions. {x, y})"
    apply (simp add: fusions_of_def)
    by (simp add: case_prod_beta)

  have
    "FL (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) =
     set zs \<union> \<Union> (FL ` set (fusions_of fusions))"
    by (simp add: FL_Mols1)
  also have
    "... = set zs \<union> (\<Union> (x, y) \<in> set fusions. {x, y})"
    by (simp add: FL_fusions)
  finally have P11:
    "FL (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) =
     set zs \<union> (\<Union> (x, y) \<in> set fusions. {x, y})"
    by simp

  have "\<Union> (FL ` set Ts) = \<Union> (set (map FL Ts))"
    by simp
  also have "... = \<Union> (set (map FLty taus))"
    using A3 by presburger
  also have "... = \<Union> (FLty ` set taus)"
     by simp
  finally have P6: "\<Union> (FL ` set Ts) = \<Union> (FLty ` set taus)"
    by simp

  have "FL (Mols1 (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) Ts) =
        FL (Mols1 (Atom (GConstr C) zs) (fusions_of fusions))
	\<union> \<Union> (FL ` set (Ts))"
    by (simp add: FL_Mols1)
  also have
    "... = (set zs \<union> (\<Union> (x, y) \<in> set fusions. {x, y})) \<union> \<Union> (FL ` set Ts)"
   using P11 by presburger
  also have
    "... = set zs \<union> (\<Union> (x, y) \<in> set fusions. {x, y}) \<union> \<Union> (FLty ` set taus)"
   using P6 by presburger
  finally have
     "FL (Mols1 (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) Ts) =
     set zs \<union> (\<Union> (x, y) \<in> set fusions. {x, y}) \<union> \<Union> (FLty ` set taus)"
     by blast
  then have P30:
     "FL (Nus1 i (Mols1 (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) Ts)) =
      {n. n + i \<in> set zs \<union> (\<Union> (x, y) \<in> set fusions. {x, y})
                 \<union> (\<Union> ty \<in> set taus. FLty ty)}"
    by (simp add: FL_Nus1)


  have "FL (app_prodrule Ts rhs) = FL (app_prodrule Ts (i, (C, zs), fusions, taus))"
    using prod_rhs2 by auto
  also have "... =
    FL (Nus1 i (Mols1 (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) Ts))"
    by (simp add: app_prodrule_def)
  also have "... =
     {n. n + i \<in> set zs \<union> (\<Union> (x, y) \<in> set fusions. {x, y})
                 \<union> (\<Union> ty \<in> set taus. FLty ty)}"
        using P30 by blast
  also have "... = FLrhs (i, (C, zs), fusions, taus)"
    by (simp add: FLrhs_def)
  also have "... = FLrhs rhs"
    using prod_rhs2 by blast
  finally show ?thesis by simp
qed


subsection\<open>Link Substitution Over Link Substitution\<close>


lemma lmap_lmap_commute_link_aux:
   assumes "v \<in> set (map fst s)"
   shows "f (lsubst s v) =
          lsubst (map (\<lambda>(x,y). (x, f y)) s) v"
using assms
proof (induct s)
  case Nil
  then show ?case
  by auto
next
  case (Cons a s)
  then show ?case
  apply auto
  apply (simp_all add: case_prod_beta lsubst_simp)
  by (simp add: rev_image_eqI)
qed


lemma lmap_lmap_commute_link:
   assumes "v \<in> set xs"
   assumes "length xs = length ys"
   shows "f (lsubst (zip xs ys) v) =
          lsubst (zip xs (map f ys)) v"
proof -
   have "zip xs (map f ys) = map (\<lambda>(x,y). (x, f y)) (zip xs ys)"
     by (simp add: zip_map2)
  then show ?thesis
    by (simp add: assms(1,2) lmap_lmap_commute_link_aux)
qed


lemma lmap_lmap_commute_links:
   assumes "set vs \<subseteq> set xs"
   assumes "length xs = length ys"
   shows "map f (map (lsubst (zip xs ys)) vs) =
          map (lsubst (zip xs (map f ys))) vs"
using assms
proof (induct vs arbitrary: xs ys)
  case Nil
  then show ?case
  by simp
next
  case (Cons a vs)
  then show ?case
  by (simp add: lmap_lmap_commute_link)
qed


lemma lmap_shift:
  shows "(lsubst s) x + 1 = lsubst (map (\<lambda>(z, y). (z + 1, y + 1)) s) (x + 1)"
proof (induct s)
  case Nil
  then show ?case
  by simp
next
  case (Cons a s)
  then show ?case
  by (simp_all add: lsubst_simp case_prod_beta)
qed


lemma lmap_shift2:
  "(\<lambda>x. if x = 0 then x else ((lsubst s) (x - 1) + 1)) y =
   lsubst ((0, 0) # map (\<lambda>(x, y). (x + 1, y + 1)) s) y"
apply auto
using Suc_eq_plus1 Suc_pred lmap_shift by presburger



lemma lmap_lmap_commute:
   assumes "FL G \<subseteq> set xs"
   assumes "length xs = length ys"
   shows "lmap f (lmap (lsubst (zip xs ys)) G) = lmap (lsubst (zip xs (map f ys))) G"
using assms
proof (induct G arbitrary: xs ys f rule: graph.induct[of _ "%_. True" "%_. True"])
  case Zero
  then show ?case
  by simp
next
  case (Atom p vs)
  then show ?case
  using lmap_lmap_commute_links by force
next
  case (Fusion x1 x2)
  then show ?case
  apply auto
  apply (simp add: lmap_lmap_commute_link)
  by (simp add: lmap_lmap_commute_link)
next
  case (Mol G1 G2)
  then show ?case
  by auto
next
  case (Nu g)

  have SucMinus: "\<forall>S. Suc ` (\<lambda>x. x - 1) ` (S - {0}) = S - {0}"
    apply auto
    by (simp add: image_iff)

  have "FL (Nu g) \<subseteq> set xs"
    using Nu.prems(1) by auto
  then have "{n. Suc n \<in> FL g} \<subseteq> set xs"
    by auto
  then have "(\<lambda>x. x - 1) ` (FL g - {0}) \<subseteq> set xs"
    using shift_down_alt by blast
  then have "Suc ` (\<lambda>x. x - 1) ` (FL g - {0}) \<subseteq> Suc ` set xs"
    by (meson image_mono)
  then have "(FL g - {0}) \<subseteq> Suc ` set xs"
    using SucMinus by simp
  then have "FL g \<subseteq> insert 0 (Suc ` set xs)"
    by auto
  then have P1: "FL g \<subseteq> set (0 # map Suc xs)"
    by simp

  have P5: "\<forall>ys. map (\<lambda>(x, y). (x + 1, y + 1)) (zip xs ys) = zip (map Suc xs) (map Suc ys)"
    apply auto
    by (simp add: zip_map_map)

  have IH: "lmap (\<lambda>x. if x = 0 then x else (f (x - 1) + 1))
        (lmap (lsubst (zip (0 # map Suc xs) (0 # map Suc ys))) g) =
	lmap (lsubst (zip (0 # map Suc xs)
	   (map (\<lambda>x. if x = 0 then x else (f (x - 1) + 1)) (0 # map Suc ys)))) g"
   by (metis (lifting) Nu.hyps Nu.prems(2) P1 length_Cons length_map)

  have IH2: "map (\<lambda>x. if x = 0 then x else (f (x - 1) + 1)) (0 # map Suc ys) =
             0 # map Suc (map f ys)"
     apply (induct ys) by auto

   have IH3: "\<forall>ys. lmap (lsubst (zip xs ys)) (Nu g) =
               Nu (lmap (lsubst (zip (0 # map Suc xs) (0 # map Suc ys))) g)"
   proof
     fix ys
     have "lmap (lsubst (zip xs ys)) (Nu g) =
           Nu (lmap (\<lambda>x. if x = 0 then x else (lsubst (zip xs ys) (x - 1) + 1)) g)"
       using lmap.simps(5) by blast
     also have "... =
           Nu (lmap (lsubst ((0, 0) # map (\<lambda>(x, y). (x + 1, y + 1)) (zip xs ys))) g)"
       using lmap_shift2 by presburger
     also have "... =
           Nu (lmap (lsubst ((0, 0) # zip (map Suc xs) (map Suc ys))) g)"
       using P5 by presburger
     also have "... =
           Nu (lmap (lsubst (zip (0 # map Suc xs) (0 # map Suc ys))) g)"
       by simp
     finally show
       "lmap (lsubst (zip xs ys)) (Nu g) =
        Nu (lmap (lsubst (zip (0 # map Suc xs) (0 # map Suc ys))) g)" .
   qed


  have "lmap f (lmap (lsubst (zip xs ys)) (Nu g)) =
             lmap f (Nu (lmap (lsubst (zip (0 # map Suc xs) (0 # map Suc ys))) g))"
     using IH3 by presburger
  also have "... =
        Nu (lmap (\<lambda>x. if x = 0 then x else (f (x - 1) + 1))
        (lmap (lsubst (zip (0 # map Suc xs) (0 # map Suc ys))) g))"
    using lmap.simps(5) by blast
  also have "... =
        Nu ((lmap (lsubst (zip (0 # map Suc xs)
	   (map (\<lambda>x. if x = 0 then x else (f (x - 1) + 1)) (0 # map Suc ys)))) g))"
    using IH by blast
  also have "... =
        Nu ((lmap (lsubst (zip (0 # map Suc xs) (0 # map Suc (map f ys)))) g))"
    using IH2 by argo
  also have "... = lmap (lsubst (zip xs (map f ys))) (Nu g)"
     using IH3 by presburger
  finally show ?case .
qed auto


section\<open>Properties of Lift and Graph Substitution\<close>


subsection\<open>Basic Properties of Lift\<close>

lemma lift_graph_lmap_commute:
  "lift_graph i (lmap f g) = lmap f (lift_graph i g)"
apply (induct g arbitrary: f i) by simp_all


lemma lift_graph_freelinks:
  "FL (lift_graph i g) = FL g"
apply (induct g arbitrary: i) by simp_all


lemma lifts_graph_freelinks:
  "FL ((lift_graph i ^^ n) g) = FL g"
apply (induct n)
using lift_graph_freelinks
by auto

lemma lsubst_graph_freelinks:
  assumes "length xs = length ys"
  assumes "set xs = FL G"
  assumes "distinct xs"
  shows "FL (lmap (lsubst (zip xs ys)) G) = set ys"
proof -
  have P1: "FL (lmap (lsubst (zip xs ys)) G) =
            (lsubst (zip xs ys)) ` FL G"
    by (simp add: FL_lmap_commute)
  have P2: "lsubst (zip xs ys) ` set xs = set ys"
    by (metis assms(1,3) lsubst_image map_fst_zip map_snd_zip)
  then have P3: "lsubst (zip xs ys) ` FL G = set ys"
    by (simp add: assms(2))
  then show ?thesis
    by (simp add: FL_lmap_commute)
qed


subsection\<open>Basic Properties of Graph Substitution\<close>


lemma subst_atom_freelinks:
  assumes "set xs = FL g2"
  assumes "distinct xs"
  shows "FL (subst_p i xs g2 p ys) = set ys"
proof (cases p)
  case (GConstr x1)
  then show ?thesis
  by simp
next
  case (GVar j)
  consider (lt) "i < j" | (eq) "i = j" | (gt) "j < i"
    by arith
  then show ?thesis
  proof cases
    case lt
      then show ?thesis
      by (simp add: GVar)
    next
    case eq
      then show ?thesis
      by (simp add: GVar assms(1,2) lsubst_graph_freelinks)
    next
    case gt
      then show ?thesis
      by (simp add: GVar)
   qed
next
  case (GAbs x31 x32 x33)
  then show ?thesis
  by simp
qed


lemma subst_graph_freelinks_equiv:
  assumes "set xs = FL g2"
  assumes "distinct xs"
  shows "FL (subst_graph i xs g2 g) = FL g"
using assms
proof (induct g arbitrary: i xs g2 rule: graph.induct[of _ "%_. True" "%_. True"])
  case Zero
  then show ?case
  by auto
next
  case (Atom x1 x2)
  then show ?case
  by (simp add: subst_atom_freelinks)
next
  case (Fusion x1 x2)
  then show ?case
  by simp
next
  case (Mol g1 g2)
  then show ?case
  by simp
next
  case (Nu g)
  then show ?case
  by simp
qed auto


lemma lift_graph_cong:
  fixes g1 g2 :: "'ty graph"
  assumes "g1 \<simeq> g2"
  shows   "lift_graph i g1 \<simeq> lift_graph i g2"
  using assms
proof (induction arbitrary: i rule: gcong.induct)
  case (refl g)
  then show ?case
  apply auto
  done
next
  case (sym g1 g2)
  then show ?case
  apply auto
  done
next
  case (trans g1 g2 g3)
  then show ?case
  using gcong.trans by blast
next
  case (mol_zero g)
  then show ?case
  by simp
next
  case (mol_comm g1 g2)
  then show ?case
  by simp
next
  case (mol_assoc a b c)
  then show ?case
  by simp
next
  case (mol_cong g1 g1' g2 g2')
  then show ?case
  by (simp add: gcong.mol_cong)
next
  case (nu_cong g g')
  then show ?case
  by (simp add: gcong.nu_cong)
next
  case (nu_subst_fusion1 y g)
  have P1: "lift_graph i (Nu (lmap (\<lambda>x. if x = 0 then y else x) g)) =
            Nu (lift_graph i (lmap (\<lambda>x. if x = 0 then y else x) g))"
      using lift_graph.simps(5) by blast
  have P2: "... = Nu (lmap (\<lambda>x. if x = 0 then y else x) (lift_graph i g))"
      by (simp add: lift_graph_lmap_commute)
  have P3: "y \<in> FL (lift_graph i g)"
     by (simp add: lift_graph_freelinks local.nu_subst_fusion1)
  then have P5: "Nu (lmap (\<lambda>x. if x = 0 then y else x) (lift_graph i g)) \<simeq>
                 Nu (Mol (Fusion 0 y) (lift_graph i g))"
     using gcong.nu_subst_fusion1 by blast
  have P6: "... = lift_graph i (Nu (Mol (Fusion 0 y) g))"
     by simp
  then show ?case
     by (simp add: P2 P5 gcong.sym)
next
  case (nu_subst_fusion2 g y)
  have P1: "lift_graph i (Nu (lmap (\<lambda>x. if x = 0 then y else x) g)) =
            Nu (lift_graph i (lmap (\<lambda>x. if x = 0 then y else x) g))"
      using lift_graph.simps(5) by blast
  have P2: "... = Nu (lmap (\<lambda>x. if x = 0 then y else x) (lift_graph i g))"
      by (simp add: lift_graph_lmap_commute)
  have P3: "0 \<in> FL (lift_graph i g)"
     by (simp add: lift_graph_freelinks local.nu_subst_fusion2)
  then have P5: "Nu (lmap (\<lambda>x. if x = 0 then y else x) (lift_graph i g)) \<simeq>
                 Nu (Mol (Fusion 0 y) (lift_graph i g))"
     using gcong.nu_subst_fusion2 by blast
  have P6: "... = lift_graph i (Nu (Mol (Fusion 0 y) g))"
     by simp
  then show ?case
     by (simp add: P2 P5 gcong.sym)
next
  case nu_nu_fusion1
  then show ?case
  using gcong.nu_nu_fusion1 by auto
next
  case nu_nu_fusion2
  then show ?case
  by simp
next
  case nu_zero
  then show ?case
  by simp
next
  case (nu_comm g)
  then show ?case
  by (simp add: gcong.nu_comm lift_graph_lmap_commute)
next
  case (nu_scope g2 g1)
  then show ?case
  apply auto
  by (simp add: gcong.nu_scope lift_graph_lmap_commute)
qed



section \<open>Theorems of Congruence\<close>


subsection \<open>Free Links Equivalence of Congruent Graphs\<close>


text \<open>
We show that the set of free links over congruent graphs are equivalent.
\<close>


lemma freelinks_equiv_E6A:
  assumes A1: "G1 = Nu (Mol (Fusion 0 y) g)"
      and A2: "G2 = Nu (lmap (\<lambda> x. if x = 0 then y else x) g)"
      and A3: "y \<in> FL g"
  shows "FL G1 = FL G2"
proof -
  have "{n. Suc n \<in> (\<lambda> x. if x = 0 then y else x) ` FL g} =
        {n. Suc n \<in> FL (Mol (Fusion 0 y) g)}"
     apply simp
     using A3 by blast
  then show ?thesis
     by (simp add: A1 A2 FL_lmap_commute)
qed


lemma freelinks_equiv_E6B:
  assumes A1: "G1 = Nu (Mol (Fusion 0 y) g)"
      and A2: "G2 = Nu (lmap (\<lambda> x. if x = 0 then y else x) g)"
      and A3: "0 \<in> FL g"
  shows "FL G1 = FL G2"
proof -
  have P1: "FL (lmap (\<lambda> x. if x = 0 then y else x) g) =
            (\<lambda> x. if x = 0 then y else x) ` FL g"
      using FL_lmap_commute by blast
  have P2: "{n. Suc n \<in> (\<lambda> x. if x = 0 then y else x) ` FL g} =
            {n. Suc n \<in> FL (Mol (Fusion 0 y) g)}"
     apply auto
     using A3 by blast
  then show ?thesis
     by (simp add: A1 A2 FL_lmap_commute)
qed


lemma freelinks_equiv_E9:
  assumes "G1 = Nu (Nu g)"
      and "G2 = Nu (Nu (lmap (\<lambda>x. if x = 0 then 1 else if x = 1 then x else x) g))"
  shows "FL G1 = FL G2"
proof -
  have P1: "FL (lmap (\<lambda>x. if x = 0 then 1 else if x = 1 then x else x) g) =
            (\<lambda>x. if x = 0 then 1 else if x = 1 then x else x)` FL g"
     using FL_lmap_commute by blast

  have P2: "FL (Nu (Nu (lmap (\<lambda>x. if x = 0 then 1 else if x = 1 then x else x) g))) =
            {n. Suc (Suc n) \<in> (\<lambda>x. if x = 0 then 1 else if x = 1 then x else x) ` FL g}"
     using Collect_cong FL.simps(5) P1 mem_Collect_eq by auto
  have P3: "... = {n. Suc (Suc n) \<in> (\<lambda>x. if x = 0 then 1 else if x = 1 then x else x) ` FL g}"
      using P1 by simp
  have P4: "... = {n. Suc (Suc n) \<in> FL g}"
     using diff_Suc_1' by fastforce
  have P5: "... = FL (Nu (Nu g))"
    by auto
  show ?thesis
    using P2 P4 P5 assms(1,2) by argo
qed



lemma freelinks_equiv_E10:
  assumes A1: "G1 = Mol (Nu g1) g2"
      and A2: "G2 = Nu (Mol g1 (lmap Suc g2))"
  shows "FL G1 = FL G2"
proof -
  have "FL G2 = FL (Nu (Mol g1 (lmap Suc g2)))"
    by (simp add: A2)
  also have "... = {n. Suc n \<in> FL (Mol g1 (lmap Suc g2))}"
    by simp
  also have "... = {n. Suc n \<in> (FL g1 \<union> FL (lmap Suc g2))}"
    by simp
  also have "... = {n. Suc n \<in> FL g1} \<union> {n. Suc n \<in> FL (lmap Suc g2)}"
    by auto
  also have "... = FL (Nu g1) \<union> {n. Suc n \<in> FL (lmap Suc g2)}"
    by simp
  also have "... = FL (Nu g1) \<union> FL (Nu (lmap Suc g2))"
    by simp
  also have "... = FL (Nu g1) \<union> FL g2"
    by (simp add: FL_lmap_deSuc_Suc)
  also have "... = FL (Mol (Nu g1) g2)"
    by simp
  also have "... = FL G1"
    by (simp add: A1)
  finally show ?thesis
    by simp
qed


text \<open>Equivalence of free links over congruent graphs. \<close>
lemma freelinks_equiv:
  assumes "g1 \<simeq> g2"
  shows "FL g1 = FL g2"
using assms
proof (induction rule: gcong.induct)
  case (refl g)
  then show ?case by simp
next
  case (sym g1 g2)
  then show ?case by simp
next
  case (trans g1 g2 g3)
  then show ?case
  by presburger
next
  case (mol_zero g)
  then show ?case by simp
next
  case (mol_comm g1 g2)
  then show ?case
  by (simp add: sup_commute)
next
  case (mol_assoc a b c)
  then show ?case by (simp add: sup_assoc)
next
  case (mol_cong g1 g2 g1' g2')
  then show ?case
  using FL.simps(4) by blast
next
  case (nu_cong g g')
  then show ?case
  using FL.simps(5) by blast
next
  case (nu_subst_fusion1 y g)
  then show ?case
  using freelinks_equiv_E6A by blast
next
  case (nu_subst_fusion2 y g)
  then show ?case
  using freelinks_equiv_E6B by blast
next
  case (nu_nu_fusion1)
  then show ?case
  by auto
next
  case (nu_nu_fusion2)
  then show ?case by simp
next
  case (nu_zero)
  then show ?case by simp
next
  case (nu_comm g)
  then show ?case
  using freelinks_equiv_E9 by blast
next
  case (nu_scope g1 g2)
  then show ?case
  using freelinks_equiv_E10 by blast
qed 
(*
auto
*)


subsection \<open>Multiset Invariant Over Congruent Graphs\<close>


text\<open>
Checks that the left-most atom is a constructor atom.
Used to distinguish the graph created by app\_prod and an abstraction atom.
\<close>
primrec f_of :: "'ty graph => ('ty p * nat) multiset"
where
  "f_of Zero = {#}"
| "f_of (Atom p xs) = {# (p, length xs) #}"
| "f_of (Fusion x y) = {#}"
| "f_of (Mol g1 g2) = f_of g1 + f_of g2"
| "f_of (Nu g) = f_of g"



lemma lmap_id: "lmap id g = g"
apply (induct g)
apply auto
by (metis (full_types, lifting) ext Suc_eq_plus1 Suc_pred' neq0_conv)


lemma f_lmap_ignore[simp]:
  "f_of (lmap f g) = f_of g"
by (induct g arbitrary: f) auto


lemma f_cong_gcong:
  assumes "g1 \<simeq> g2"
  shows "f_of g1 = f_of g2"
using assms
apply (induct set: gcong)
by auto


lemma abs_cong_inv:
  assumes "Atom (GAbs xs1 ty1 e1) ys1 \<simeq> Atom (GAbs xs2 ty2 e2) ys2"
  shows "xs1 = xs2 \<and> ty1 = ty2 \<and> e1 = e2 \<and> length ys1 = length ys2"
proof -
  have P1: "f_of (Atom (GAbs xs1 ty1 e1) ys1) = f_of (Atom (GAbs xs2 ty2 e2) ys2)"
    using assms f_cong_gcong by blast
  have P2: "f_of (Atom (GAbs xs1 ty1 e1) ys1) = {# (GAbs xs1 ty1 e1, length ys1) #}"
    by simp
  have P3: "f_of (Atom (GAbs xs2 ty2 e2) ys2) = {# (GAbs xs2 ty2 e2, length ys2) #}"
    by simp
  have P4: "{# (GAbs xs1 ty1 e1, length ys1) #} = {# (GAbs xs2 ty2 e2, length ys2) #}"
    using P1 P2 P3 by argo
  then show ?thesis
    by fastforce
qed


lemma abs_var_cong_inv:
  "\<not>(Atom (GVar i) ys' \<simeq> Atom (GAbs xs ty1 e) ys)"
proof -
  have "\<not>((GVar i, length ys') = (GAbs xs ty1 e, length ys))"
     by force
  then have "\<not>({# (GVar i, length ys') #} = {# (GAbs xs ty1 e, length ys) #})"
    by simp
  then have "\<not> f_of (Atom (GVar i) ys') = f_of (Atom (GAbs xs ty1 e) ys)"
    by simp
  then show ?thesis
    using f_cong_gcong by blast
qed


subsection \<open>Lemmata with Lift Graph\<close>


lemma lift_graph_Nus1_equiv:
  "lift_graph i (Nus1 j G) = Nus1 j (lift_graph i G)"
apply (induct j)
by simp_all


lemma lift_graph_Mols1_equiv:
  "lift_graph i (Mols1 G Gs) = Mols1 (lift_graph i G) (map (lift_graph i) Gs)"
apply (induct Gs arbitrary: G)
by (simp_all add: Mols1)


lemma lift_graph_fusions_of:
  "map (lift_graph i) (fusions_of fusions) = fusions_of fusions"
proof (induction fusions)
  case Nil
  then show ?case
    by (simp add: fusions_of_def)
next
  case (Cons p ps)
  obtain x y where p_eq: "p = (x, y)"
    by (cases p) auto
  then show ?case
    by (simp add: case_prod_beta fusions_of_def)
qed


lemma lift_graph_app_prodrule_equiv:
  "lift_graph i (app_prodrule Ts rhs) =
   app_prodrule (map (lift_graph i) Ts) rhs"
proof -
  obtain j C zs fusions taus
    where rhs_eq: "rhs = (j, (C, zs), fusions, taus)"
    by (cases rhs) auto

  have P1: "lift_graph i (Atom (GConstr C) zs) = Atom (GConstr C) zs"
    by simp

  have P2: "map (lift_graph i) (fusions_of fusions) = fusions_of fusions"
    by (simp add: lift_graph_fusions_of)

  have P3:
    "lift_graph i (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) =
     Mols1 (lift_graph i (Atom (GConstr C) zs))
           (map (lift_graph i) (fusions_of fusions))"
    by (simp add: lift_graph_Mols1_equiv)

  from P1 P2 P3 have P4:
    "lift_graph i (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) =
     Mols1 (Atom (GConstr C) zs) (fusions_of fusions)"
    by (simp add: lift_graph_fusions_of)

  have P5:
    "lift_graph i
       (Nus1 j (Mols1 (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) Ts)) =
     Nus1 j
       (Mols1 (lift_graph i (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)))
              (map (lift_graph i) Ts))"
    by (simp add: lift_graph_Mols1_equiv lift_graph_Nus1_equiv)

  from P4 P5 have P6:
    "lift_graph i
       (Nus1 j (Mols1 (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) Ts)) =
     Nus1 j
       (Mols1 (Mols1 (Atom (GConstr C) zs) (fusions_of fusions))
              (map (lift_graph i) Ts))"
    by metis

  show ?thesis
    unfolding rhs_eq app_prodrule_def
    using P6 by simp
qed


subsection \<open>Lemmata with Subst Graph\<close>


lemma subst_graph_Nus1_equiv:
  "subst_graph i xs g2 (Nus1 j G) = Nus1 j (subst_graph i xs g2 G)"
apply (induct j)
by simp_all


lemma subst_graph_Mols1_equiv:
  "subst_graph i xs g2 (Mols1 G Gs) = Mols1 (subst_graph i xs g2 G) (map (subst_graph i xs g2) Gs)"
apply (induct Gs arbitrary: G)
by (simp_all add: Mols1)


lemma subst_graph_fusions_of:
  "map (subst_graph i xs g2) (fusions_of fusions) = fusions_of fusions"
proof (induct fusions)
  case Nil
  then show ?case
  by (simp add: fusions_of_def)
next
  case (Cons a fusions)
  then show ?case
  apply (simp_all add: fusions_of_def)
  by (simp add: case_prod_beta)
qed


lemma subst_typrod:
 "subst_graph i xs g2 (app_prodrule Ts rhs) =
  app_prodrule (map (subst_graph i xs g2) Ts) rhs"
proof -
  obtain j C zs fusions taus
    where rhs_eq: "rhs = (j, (C, zs), fusions, taus)"
    by (cases rhs) auto

  have P1: "subst_graph i xs g2 (Atom (GConstr C) zs) = Atom (GConstr C) zs"
    by simp

  have P2: "map (subst_graph i xs g2) (fusions_of fusions) = fusions_of fusions"
    by (simp add: subst_graph_fusions_of)

  have P3:
    "subst_graph i xs g2 (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) =
     Mols1 (subst_graph i xs g2 (Atom (GConstr C) zs))
           (map (subst_graph i xs g2) (fusions_of fusions))"
    by (simp add: subst_graph_Mols1_equiv)

  from P1 P2 P3 have P4:
    "subst_graph i xs g2 (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) =
     Mols1 (Atom (GConstr C) zs) (fusions_of fusions)"
    by simp


  have P5:
    "subst_graph i xs g2
       (Nus1 j (Mols1 (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) Ts)) =
     Nus1 j
       (Mols1 (subst_graph i xs g2 (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)))
              (map (subst_graph i xs g2) Ts))"
    by (simp add: subst_graph_Mols1_equiv subst_graph_Nus1_equiv)


  from P4 P5 have P6:
    "subst_graph i xs g2
       (Nus1 j (Mols1 (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) Ts)) =
     Nus1 j
       (Mols1 (Mols1 (Atom (GConstr C) zs) (fusions_of fusions))
              (map (subst_graph i xs g2) Ts))"
    by metis
  then show ?thesis
    unfolding rhs_eq app_prodrule_def
    using P6 by simp
qed


subsection \<open>Lemmata of Link substitutions\<close>


lemma subst_p_lmap_commute:
 assumes "FL G \<subseteq> set xs"
 shows "lmap f (subst_p i xs G p ys) = subst_p i xs G p (map f ys)"
using assms
proof (cases p)
  case (GConstr x1)
  then show ?thesis
  by simp
next
  case (GVar j)
  consider (lt) "i < j" | (eq) "i = j" | (gt) "j < i"
    by arith
  then show ?thesis
  proof cases
    case lt
      then show ?thesis
      by (simp add: GVar)
    next
    case eq
      then show ?thesis
      by (simp add: GVar assms(1) lmap_lmap_commute)
    next
    case gt
      then show ?thesis
      by (simp add: GVar)
   qed
next
  case (GAbs x31 x32 x33)
  then show ?thesis
  by simp
qed


lemma subst_graph_lmap_commute:
  assumes "FL G \<subseteq> set xs"
  shows "lmap f (subst_graph i xs G g1) = subst_graph i xs G (lmap f g1)"
using assms
proof (induct g1 arbitrary: f rule: graph.induct[of _ "%_. True" "%_. True"])
  case Zero
  then show ?case
  by auto
next
  case (Atom x1 x2)
  then show ?case
  apply auto
  by (simp add: subst_p_lmap_commute)
next
  case (Fusion x1 x2)
  then show ?case
  by auto
next
  case (Mol g11 g12)
  then show ?case
  by auto
next
  case (Nu g1)
  then show ?case
  by auto
qed auto


lemma lmap_compose:
  "lmap f (lmap g G) = lmap (f o g) G"
proof (induct G arbitrary: f g rule: graph.induct[of _ "%_. True" "%_. True"])
  case Zero
  then show ?case
  by simp
next
  case (Atom x1 x2)
  then show ?case
  by auto
next
  case (Fusion x1 x2)
  then show ?case
  by auto
next
  case (Mol G1 G2)
  then show ?case
  by auto
next
  case (Nu G)
  have P2: "(\<lambda>x. if x = 0 then x else f (x - 1) + 1) o (\<lambda>x. if x = 0 then x else g (x - 1) + 1) =
    (\<lambda>x. if x = 0 then x else f (g (x - 1)) + 1)"
    using Suc_eq_plus1 Zero_not_Suc diff_Suc_1 by auto
  show ?case
  apply auto
  using Nu P2 by presburger
qed auto


lemma lmap_lim:
  "\<forall>x \<in> FL G. f x = g x ==> lmap f G = lmap g G"
apply (induct G arbitrary: f g)
by simp_all


lemma lmap_graph_cong:
  "g1 \<simeq> g2 ==> lmap f g1 \<simeq> lmap f g2"
proof (induct arbitrary: f rule: gcong.induct)
  case (refl g)
  then show ?case
  by blast
next
  case (sym g1 g2)
  then show ?case
  by blast
next
  case (trans g1 g2 g3)
  then show ?case
  using gcong.trans by blast
next
  case (mol_zero g)
  then show ?case
  by simp
next
  case (mol_comm g1 g2)
  then show ?case
  by simp
next
  case (mol_assoc a b c)
  then show ?case
  by simp
next
  case (mol_cong g1 g1' g2 g2')
  then show ?case
  by (simp add: gcong.mol_cong)
next
  case (nu_cong g g')
  then show ?case
  by auto
next
  case (nu_subst_fusion1 y g)

  have "y \<in> FL g"
    by (simp add: local.nu_subst_fusion1)
  then have P4: "(\<lambda>x. if x = 0 then x else f (x - 1) + 1) y
             \<in> FL (lmap (\<lambda>x. if x = 0 then x else f (x - 1) + 1) g)"
    using FL_lmap_commute by blast

  have P6: "(\<lambda>x. if x = 0 then (\<lambda>x. if x = 0 then x else f (x - 1) + 1) y else x)
	    o (\<lambda>x. if x = 0 then x else f (x - 1) + 1) =
           (\<lambda>x. if x = 0 then x else f (x - 1) + 1) o (\<lambda>x. if x = 0 then y else x)"
    by auto

  have T1: "lmap f (Nu (Mol (Fusion 0 y) g)) =
            Nu (Mol (Fusion 0 ((\<lambda>x. if x = 0 then x else f (x - 1) + 1) y))
	       (lmap (\<lambda>x. if x = 0 then x else f (x - 1) + 1) g))"
    by auto
  also have T2: "... \<simeq>
            Nu (lmap (\<lambda>x. if x = 0 then (\<lambda>x. if x = 0 then x else f (x - 1) + 1) y else x)
	       (lmap (\<lambda>x. if x = 0 then x else f (x - 1) + 1) g))"
      using P4 gcong.nu_subst_fusion1 by blast
  have T3: "... =
            Nu (lmap
	         ((\<lambda>x. if x = 0 then (\<lambda>x. if x = 0 then x else f (x - 1) + 1) y else x)
	          o (\<lambda>x. if x = 0 then x else f (x - 1) + 1)) g)"
      using lmap_compose by blast
  have T4: "... =
            Nu (lmap
	         ((\<lambda>x. if x = 0 then x else f (x - 1) + 1) o (\<lambda>x. if x = 0 then y else x)) g)"
    by (simp add: P6)
  have T5: "... =
            Nu (lmap (\<lambda>x. if x = 0 then x else f (x - 1) + 1)
	       (lmap (\<lambda>x. if x = 0 then y else x) g))"
    by (simp add: lmap_compose)
  have T6: "... = lmap f (Nu (lmap (\<lambda>x. if x = 0 then y else x) g))"
    by simp
  show ?case
    using P6 T2 T3 T5 T6 calculation by argo
next
  case (nu_subst_fusion2 g y)
  have "0 \<in> FL g"
    by (simp add: local.nu_subst_fusion2)
  then have P4: "0
             \<in> FL (lmap (\<lambda>x. if x = 0 then x else f (x - 1) + 1) g)"
    by (simp add: FL_lmap_commute)

  have P6: "(\<lambda>x. if x = 0 then (\<lambda>x. if x = 0 then x else f (x - 1) + 1) y else x)
	    o (\<lambda>x. if x = 0 then x else f (x - 1) + 1) =
           (\<lambda>x. if x = 0 then x else f (x - 1) + 1) o (\<lambda>x. if x = 0 then y else x)"
    by auto

  have T1: "lmap f (Nu (Mol (Fusion 0 y) g)) =
            Nu (Mol (Fusion 0 ((\<lambda>x. if x = 0 then x else f (x - 1) + 1) y))
	       (lmap (\<lambda>x. if x = 0 then x else f (x - 1) + 1) g))"
    by auto
  also have T2: "... \<simeq>
            Nu (lmap (\<lambda>x. if x = 0 then (\<lambda>x. if x = 0 then x else f (x - 1) + 1) y else x)
	       (lmap (\<lambda>x. if x = 0 then x else f (x - 1) + 1) g))"
      using P4 gcong.nu_subst_fusion2 by blast
  have T3: "... =
            Nu (lmap
	         ((\<lambda>x. if x = 0 then (\<lambda>x. if x = 0 then x else f (x - 1) + 1) y else x)
	          o (\<lambda>x. if x = 0 then x else f (x - 1) + 1)) g)"
      using lmap_compose by blast
  have T4: "... =
            Nu (lmap
	         ((\<lambda>x. if x = 0 then x else f (x - 1) + 1) o (\<lambda>x. if x = 0 then y else x)) g)"
    by (simp add: P6)
  have T5: "... =
            Nu (lmap (\<lambda>x. if x = 0 then x else f (x - 1) + 1)
	       (lmap (\<lambda>x. if x = 0 then y else x) g))"
    by (simp add: lmap_compose)
  have T6: "... = lmap f (Nu (lmap (\<lambda>x. if x = 0 then y else x) g))"
    by simp
  show ?case
    using P6 T2 T3 T5 T6 calculation by argo
next
  case nu_nu_fusion1
  then show ?case
  apply auto
  using gcong.nu_nu_fusion1 by auto
next
  case nu_nu_fusion2
  then show ?case
  by auto
next
  case nu_zero
  then show ?case
  by auto
next
  case (nu_comm g)

  have P1:
    "(\<lambda>x. if x = 0 then 1 else if x = 1 then x else x)
     o (\<lambda>x. if x = 0 then x else (if x - 1 = 0 then x - 1 else f (x - 1 - 1) + 1) + 1) =
     (\<lambda>x. if x = 0 then x else (if x - 1 = 0 then x - 1 else f (x - 1 - 1) + 1) + 1)
     o (\<lambda>x. if x = 0 then 1 else if x = 1 then x else x)"
    by auto

  show ?case
  apply auto
   by (metis (no_types, lifting) P1 gcong.nu_comm lmap_compose)
next
  case (nu_scope g1 g2)
  have "lmap (Suc o f) g2 = lmap ((\<lambda>x. if x = 0 then x else f (x - 1) + 1) o Suc) g2"
     by (simp add: lmap_lim)
  then have P3: "lmap Suc (lmap f g2) = lmap (\<lambda>x. if x = 0 then x else f (x - 1) + 1) (lmap Suc g2)"
     by (simp add: lmap_compose)

  have E1:
    "lmap f (Mol (Nu g1) g2) =
     Mol (Nu (lmap (\<lambda>x. if x = 0 then x else f (x - 1) + 1) g1)) (lmap f g2)"
     by simp
  have E2: "... \<simeq>
     Nu (Mol (lmap (\<lambda>x. if x = 0 then x else f (x - 1) + 1) g1)
         (lmap (\<lambda>x. if x = 0 then x else f (x - 1) + 1) (lmap Suc g2)))"
    by (metis gcong.nu_scope P3)
  have E3: "... = Nu (lmap (\<lambda>x. if x = 0 then x else f (x - 1) + 1) (Mol g1 (lmap Suc g2)))"
    by simp
  have E4: "... = lmap f (Nu (Mol g1 (lmap Suc g2)))"
    by simp

  show ?case
    using E1 E2 E3 E4 by argo
qed 
(*
auto
*)


subsection \<open>Graph Substitution Over Congruence Graphs and Expressions\<close>


lemma subst_graph_cong:
  assumes "g1 \<simeq> g2"
  assumes "set xs = FL G"
  assumes "distinct xs"
  shows "subst_graph i xs G g1 \<simeq> subst_graph i xs G g2"
using assms
proof (induction arbitrary: i xs G rule: gcong.induct)
  case (refl g)
  then show ?case
  by (simp add: gcong.refl)
next
  case (sym g1 g2)
  then show ?case
  by blast
next
  case (trans g1 g2 g3)
  then show ?case
  using gcong.trans by blast
next
  case (mol_zero g)
  then show ?case
  by simp
next
  case (mol_comm g1 g2)
  then show ?case
  by simp
next
  case (mol_assoc a b c)
  then show ?case
  by simp
next
  case (mol_cong g1 g1' g2 g2')
  then show ?case
  by (simp add: gcong.mol_cong)
next
  case (nu_cong g g')
  then show ?case
  by (simp add: gcong.nu_cong)
next
  case (nu_subst_fusion1 y g)
  then show ?case
  apply auto
  by (metis (no_types, lifting) gcong.nu_subst_fusion1 order_refl subst_graph_freelinks_equiv
    subst_graph_lmap_commute)
next
  case (nu_subst_fusion2 g y)
  then show ?case
  apply auto
  by (metis (no_types, lifting) dual_order.refl gcong.nu_subst_fusion2 subst_graph_freelinks_equiv
    subst_graph_lmap_commute)
next
  case nu_nu_fusion1
  then show ?case
  apply auto
  using gcong.nu_nu_fusion1 by fastforce
next
  case nu_nu_fusion2
  then show ?case
  by auto
next
  case nu_zero
  then show ?case
  by simp
next
  case (nu_comm g)
  then show ?case
  apply auto
  by (metis (no_types, lifting) gcong.nu_comm subsetI subst_graph_lmap_commute)
next
  case (nu_scope g2 g1)
  then show ?case
  apply auto
   by (metis gcong.nu_scope subset_refl subst_graph_lmap_commute)
qed


section \<open>Properties of Environments\<close>


lemma insert_at_shift:
  "insert_at (xs @ ys) (j + length xs) y = xs @ insert_at ys j y"
apply (induction xs)
by auto




text \<open>
  Inserting at any position increases the environment length by exactly one.)
\<close>
lemma length_insert_at:
  "length (insert_at xs j y) = length xs + 1"
proof (induction xs arbitrary: j)
  case Nil
  then show ?case
  apply (cases j)
  apply auto
  done
next
  case (Cons a xs)
  then show ?case
  apply (cases j)
  apply simp
  by simp
qed

text \<open>
  Relations between the before and the after inserted environments.
\<close>

(* If we insert y at position j (within bounds), then the element at j is y. *)
lemma shift_eq:
  assumes "j \<le> length xs"
  shows   "(insert_at xs j y) ! j = y"
using assms
proof (induction xs arbitrary: j)
  case Nil
  then show ?case
  apply (cases j)
  apply auto
  done
next
  case (Cons y ys)
  then show ?case
  apply (cases j)
  apply auto
  done
qed


(* If we insert at position i (within bounds) and look at an index j < i,
   the prefix is unchanged. *)
lemma shift_gt:
  assumes "i \<le> length xs"
  shows "j < i ==> (insert_at xs i y) ! j = xs ! j"
using assms
proof (induction xs arbitrary: i j)
  case Nil
  then show ?case
  apply (cases i)
  apply simp
  by simp
next
  case (Cons a xs)
  then show ?case
  apply (cases i)
  apply auto
  using less_Suc_eq_0_disj by fastforce
qed


(* If we insert at position i and look at an index j > i,
   indices to the right are shifted by one. *)
lemma shift_lt:
  "i < j ==>
  (insert_at xs i y) ! j = xs ! (j - 1)"
proof (induction xs arbitrary: i j)
  case Nil
  then show ?case
  apply (cases i)
  apply simp
  by simp
next
  case (Cons a xs)
  then show ?case
  apply (cases i)
  apply auto
  done
qed


text \<open>
  Inserting y at the front and then U at position Suc i is the same as
  first inserting U at position i and then y at the front.
\<close>
lemma shift_commute:
  "insert_at (insert_at xs i y1) 0 y2
   = insert_at (insert_at xs 0 y2) (Suc i) y1"
proof (induction xs arbitrary: i j)
  case Nil
  then show ?case
  by simp
next
  case (Cons a xs)
  then show ?case
  by simp
qed


section \<open>Soundness\<close>


subsection \<open>Substitution Lemma\<close>


text \<open>
  We first show that lifting preserves well-typedness.
  The lifting operation shifts free variable indices in an expression.
  This lemma shows that lifting preserves typing:
  if e is well-typed in environment $\Gamma$,
  then lifting e by i yields a well-typed term in the environment
  extended by inserting $\tau$' at position i.
  This property is crucial for the substitution lemma,
  particularly under the abstraction case.
\<close>
lemma lift_type:
  assumes T: "\<Gamma> \<turnstile>{P} e : ty"
      and LE: "i \<le> length \<Gamma>"
  shows "insert_at \<Gamma> i (ys, ty2) \<turnstile>{P} (lift i e) : ty"
using T LE
proof (induction arbitrary: i ys ty2 rule: typing.induct)
  case (TyVar j \<Gamma> xs ty vs P)
  note j_lt = TyVar.hyps(1)
  note lookup = TyVar.hyps(2)
  note len_vs = TyVar.hyps(3)
  note le_i = TyVar.prems

  show ?case
  proof (cases "j < i")
    case True
    then have P1: "lift_atom i (GVar j) = GVar j"
      by simp

    have len_ins: "length (insert_at \<Gamma> i (ys, ty2)) = length \<Gamma> + 1"
      by (simp add: length_insert_at)

    from j_lt have j_lt': "j < length (insert_at \<Gamma> i (ys, ty2))"
      by (simp add: len_ins)

    from le_i True have "(insert_at \<Gamma> i (ys, ty2)) ! j = \<Gamma> ! j"
      by (simp add: shift_gt)

    with lookup have "(insert_at \<Gamma> i (ys, ty2)) ! j = (xs, ty)"
      by simp

    with j_lt' len_vs
    show ?thesis
      using P1 TyVar.hyps(4,5,6) typing.TyVar by force
  next
    case False
    then have i_le_j: "i \<le> j" by simp

    have P1: "lift_atom i (GVar j) = GVar (Suc j)"
      by (simp add: False)

    have len_ins: "length (insert_at \<Gamma> i (ys, ty2)) = length \<Gamma> + 1"
      by (simp add: length_insert_at)

    from j_lt have "Suc j \<le> length \<Gamma>"
      by simp
    then have Sucj_lt_ins: "Suc j < length (insert_at \<Gamma> i (ys, ty2))"
      by (simp add: len_ins)

    from i_le_j have "i < Suc j" by simp
    then have "(insert_at \<Gamma> i (ys, ty2)) ! Suc j = \<Gamma> ! j"
      by (simp add: shift_lt)

    with lookup have "(insert_at \<Gamma> i (ys, ty2)) ! Suc j = (xs, ty)"
      by simp

    with Sucj_lt_ins len_vs
    show ?thesis
      using P1 TyVar.hyps(4,5,6) typing.TyVar by auto
  qed

next
  case (TyArrow xs ty1 \<Gamma> P e ty2' vs)
  note IH = TyArrow.IH
  note le = TyArrow.prems

  have Suc_le: "Suc i \<le> length ((xs, ty1) # \<Gamma>)"
    using le by simp

  have body_typed:
    "insert_at ((xs, ty1) # \<Gamma>) (Suc i) (ys, ty2) \<turnstile>{P} lift (Suc i) e : ty2'"
   using IH Suc_le by blast

  have env_eq:
    "insert_at ((xs, ty1) # \<Gamma>) (Suc i) (ys, ty2)
     = insert_at (insert_at \<Gamma> i (ys, ty2)) 0 (xs, ty1)"
    by (simp add: shift_commute)

  have "(xs, ty1) # insert_at \<Gamma> i (ys, ty2) \<turnstile>{P} lift (Suc i) e : ty2'"
     using body_typed by auto

  then show ?case
    by (simp add: TyArrow.hyps(2,3) typing.TyArrow)

next
  case (TyApp \<Gamma> P e1 ty3 ty1 xs e2)
  note IH1 = TyApp.IH(1)
  note IH2 = TyApp.IH(2)
  note le = TyApp.prems

  have
    "insert_at \<Gamma> i (ys, ty2') \<turnstile>{P} lift i e1 : TArrow ty3 ty1 xs"
    "insert_at \<Gamma> i (ys, ty2') \<turnstile>{P} lift i e2 : ty3"
     apply (simp add: IH1 le)
     by (simp add: IH2 le)

  then show ?case
    apply auto
    by (meson IH1 IH2 le typing.TyApp)

next
  case (TyCong \<Gamma> P g1 ty g2)
  note IH = TyCong.IH
  note cong = TyCong.hyps(2)
  note le = TyCong.prems

  have "insert_at \<Gamma> i (ys, ty2') \<turnstile>{P} lift i (Graph g1) : ty" for ys ty2'
    using IH le by blast
  then show ?case
    by (metis lift.simps(1) lift_graph_cong local.cong typing.TyCong)

next
  case (TyAlpha \<Gamma>2 P g ty xs vs)
  note IH = TyAlpha.IH
  note le = TyAlpha.prems(1)
  note xs_FL = TyAlpha.hyps(2)
  note len_xs_vs = TyAlpha.hyps(3)

  have "insert_at \<Gamma>2 i (ys, ty2') \<turnstile>{P} lift i (Graph g) : ty" for ys ty2'
      using IH le by blast

  (* Intuitively, lifting and link-substitution commute in a way that preserves typing.
     Depending on how much you want to commit to, you might introduce a separate lemma
     about lift_graph and lmap commuting. For a first version, you can simply
     keep TyAlpha out of the lifting lemma or assume g is closed. *)

  then show ?case
    by (simp add: TyAlpha.hyps(4,5) len_xs_vs lift_graph_freelinks lift_graph_lmap_commute typing.TyAlpha
      xs_FL)
next
  case (TyProd a xs rhs P taus Ts \<Gamma>)

  have P2:
   "lift_graph i (app_prodrule Ts rhs) = app_prodrule (map (lift_graph i) Ts) rhs"
    by (simp add: lift_graph_app_prodrule_equiv)

  then show ?case
    using P2 TyProd.IH TyProd.hyps(1,2,3,4) TyProd.prems typing.TyProd by auto
next
  case (TyCase \<Gamma> P e0 ty1 \<Gamma>2 e1 ty2' e2 T)
  have IHe0: "insert_at \<Gamma> i (ys, ty2) \<turnstile>{P} lift i e0 : ty1"
    by (simp add: TyCase.IH(1) TyCase.prems)

  have "insert_at (\<Gamma>2 @ \<Gamma>) (i + length \<Gamma>2) (ys, ty2)
              \<turnstile>{P} lift (i + length \<Gamma>2) e1 : ty2'"
    by (simp add: TyCase.IH(2) TyCase.prems)
  then have IHe1:
     "\<Gamma>2 @ insert_at \<Gamma> i (ys, ty2)
      \<turnstile>{P} lift (i + length \<Gamma>2) e1 : ty2'"
    by (simp add: insert_at_shift)

  have IHe2: "insert_at \<Gamma> i (ys, ty2) \<turnstile>{P} lift i e2 : ty2'"
    by (simp add: TyCase.IH(3) TyCase.prems)

  have
    "insert_at \<Gamma> i (ys, ty2) \<turnstile>{P}
     Case (lift i e0) \<Gamma>2 T (lift (i + length \<Gamma>2) e1) (lift i e2) : ty2'"
    using IHe0 IHe1 IHe2 typing.TyCase by blast
  then have "insert_at \<Gamma> i (ys, ty2) \<turnstile>{P} lift i (Case e0 \<Gamma>2 T e1 e2) : ty2'"
    by simp
  then show ?case .
qed


lemma weakening_left:
  assumes A1: "\<Gamma> \<turnstile>{P} e : ty"
  shows "x # \<Gamma> \<turnstile>{P} (lift 0 e) : ty"
by (metis assms insert_at.simps(1) lift_type surj_pair zero_le)


lemma lifts_graph2:
  "(lift 0 ^^ n) (Graph g) = Graph ((lift_graph 0 ^^ n) g)"
proof (induct n arbitrary: g)
  case 0
  then show ?case
  apply auto
  done
next
  case (Suc n)
  then show ?case
  apply auto
  done
qed


lemma weakening_lefts:
  assumes A1: "\<Gamma> \<turnstile>{P} e : ty"
  shows "\<Gamma>2 @ \<Gamma> \<turnstile>{P} (lift 0 ^^ length \<Gamma>2) e : ty"
using assms
proof (induct \<Gamma>2 arbitrary: e)
  case Nil
  then show ?case
  apply auto
  done
next
  case (Cons a \<Gamma>2)
  then show ?case
  apply auto
  by (simp add: weakening_left)
qed


lemma subst_lemma:
  fixes i   :: nat
    and e1  :: "type exp"
    and g2  :: "type graph"
    and ty1 ty2 :: type
    and \<Gamma>1 \<Gamma>2 :: tyenv
  assumes A1: "\<Gamma>1 \<turnstile>{P} e1 : ty1"
      and A2: "\<Gamma>2 \<turnstile>{P} Graph g2 : ty2"
      and A3: "i \<le> length \<Gamma>2"
      and A4: "\<Gamma>1 = insert_at \<Gamma>2 i (xs, ty2)"
      and A5: "set xs = FL g2"
      and A6: "distinct xs"
  shows "\<Gamma>2 \<turnstile>{P} subst i xs g2 e1 : ty1"
using assms
proof (induct arbitrary: \<Gamma>2 i ty2 g2 xs set: typing)
(*
  case (TyCong \<Gamma> P e1 ty e2)
  *)
  case (TyCong \<Gamma>' P g1' ty' g2')

  have IHFL1: "FL g2 = set xs"
    by (simp add: TyCong.prems(4))

  have P1: "\<Gamma>' \<turnstile>{P} (Graph g1') : ty'"
    by (simp add: TyCong.hyps(1))
  have P2: "\<Gamma>2 \<turnstile>{P} (subst i xs g2 ((Graph g1'))) : ty'"
    using IHFL1 TyCong.hyps(2) TyCong.prems(1,2,3,5) by presburger
  have P5: "\<Gamma>' \<turnstile>{P} (Graph g2') : ty'"
    using P1 TyCong.hyps(3) typing.TyCong by presburger


  have IH: "g1' \<simeq> g2'"
       by (simp add: TyCong.hyps(3))
  then show ?case
    by (metis IHFL1 P2 TyCong.prems(5) subst.simps(1) subst_graph_cong typing.TyCong)
next
  case (TyAlpha \<Gamma>2 P g ty xs ys)
  then show ?case
   by (metis subset_refl subst.simps(1) subst_graph_freelinks_equiv subst_graph_lmap_commute
    typing.TyAlpha)
next
  case (TyArrow xs' ty1' \<Gamma>' P e' ty2' ys')

  have PremT: "\<Gamma>2 \<turnstile>{P} (Graph g2) : ty2"
    by (simp add: TyArrow.prems(1))
  have PremLE: "0 \<le> length \<Gamma>2"
    by simp

  then have LIFT1: "insert_at \<Gamma>2 0 (xs', ty1') \<turnstile>{P} (lift 0 (Graph g2)) : ty2"
    using PremT PremLE lift_type
    by presburger
  then have LIFT: "(xs', ty1') # \<Gamma>2 \<turnstile>{P} (lift 0 (Graph g2)) : ty2"
    by simp

  have LE: "Suc i \<le> length ((xs', ty1') # \<Gamma>2)"
     by (simp add: TyArrow.prems(2,4) le_SucI length_insert_at)
  have ENV: "(xs', ty1') # \<Gamma>' = insert_at ((xs', ty1') # \<Gamma>2) (Suc i) (xs, ty2)"
     by (simp add: TyArrow.prems(3))

  have IH: "(xs', ty1') # \<Gamma>2 \<turnstile>{P} (subst (Suc i) xs (lift_graph 0 g2)) e' : ty2'"
    by (metis ENV LE LIFT1 TyArrow.hyps(2) TyArrow.prems(4,5) insert_at.simps(1) lift.simps(1)
    lift_graph_freelinks)
  show ?case
    by (metis IH Suc_eq_plus1 TyArrow.hyps(3,4) subst.simps(1) subst_graph.simps(2) subst_p.simps(2)
    typing.TyArrow)

next
  case (TyVar j \<Gamma> xs' ty' ys P)
  note TV = TyVar

  have len_\<Gamma>1: "length \<Gamma> = length \<Gamma>2 + 1"
     by (simp add: TyVar.prems(3) length_insert_at)

  have subst_GVar:
    "subst i xs g2 (Graph (Atom (GVar j) ys)) =
       (if i < j then Graph (Atom (GVar (j - 1)) ys)
        else if j = i \<and> length xs = length ys
             then Graph (lmap (lsubst (zip xs ys)) g2)
        else Graph (Atom (GVar j) ys))"
    by simp

  consider (lt) "i < j" | (eq) "i = j" | (gt) "j < i"
    by arith
  then show ?case
  proof cases
    case lt

    (* you have assumption "i < j" here *)
    then have subst_ij:
      "subst i xs g2 (Graph (Atom (GVar j) ys))
       = Graph (Atom (GVar (j - 1)) ys)"
      by (simp add: subst_GVar)

    from TyVar.hyps(1) TyVar.prems(4) len_\<Gamma>1 lt
    have j1_lt_len_\<Gamma>2: "j - 1 < length \<Gamma>2"
      by (simp add: less_diff_conv)

    from TyVar.prems(3) lt
    have lookup_shift:
      "\<Gamma> ! j = \<Gamma>2 ! (j - 1)"
      by (simp add: shift_lt)

    from TyVar.hyps(2) lookup_shift
    have "\<Gamma>2 ! (j - 1) = (xs', ty')" by simp

    moreover have "length xs' = length ys"
      using TyVar.hyps(3) .

    ultimately have
      "\<Gamma>2 \<turnstile>{P} Graph (Atom (GVar (j - 1)) ys) : lmap_ty xs' ys ty'"
     using TyVar.hyps(4,5,6) j1_lt_len_\<Gamma>2 typing.TyVar by blast

    thus ?thesis
      using subst_ij by simp
  next
    case eq
    have subst_eq:
      "subst i xs g2 (Graph (Atom (GVar j) ys)) =
         (if length xs = length ys
          then Graph (lmap (lsubst (zip xs ys)) g2)
          else Graph (Atom (GVar j) ys))"
     by (simp add: eq)

    from TyVar.hyps(2) TyVar.prems(4) eq
    have "(xs', ty') = (xs, ty2)"
    proof -
      from TyVar.prems(3)
      have "\<Gamma> ! j = (insert_at \<Gamma>2 i (xs, ty2)) ! j"
      by simp
      with eq TyVar.hyps(2) show ?thesis
        using TyVar.prems(2) shift_eq by fastforce
    qed
    then have xs'_xs: "xs' = xs" and ty'_ty2: "ty' = ty2"
      by auto

    have len_xs_ys: "length xs = length ys"
      using TyVar.hyps(3) xs'_xs by simp

    have subst_eq':
      "subst i xs g2 (Graph (Atom (GVar j) ys))
       = Graph (lmap (lsubst (zip xs ys)) g2)"
      using subst_eq len_xs_ys by simp

    have "\<Gamma>2 \<turnstile>{P} Graph (lmap (lsubst (zip xs ys)) g2)
                  : lmap_ty xs ys ty2"
      using TyVar.prems(2) TyVar.prems(4) len_xs_ys
      by (simp add: TyAlpha TyVar.hyps(5) TyVar.prems(1,5))

    then show ?thesis
      using subst_eq' ty'_ty2 xs'_xs by presburger
  next
    case gt  (* j < i: the variable is “below” the inserted one *)

    have subst_gt:
      "subst i xs g2 (Graph (Atom (GVar j) ys))
       = Graph (Atom (GVar j) ys)"
      using gt subst_GVar by simp

    from TyVar.prems(4) gt
    have lookup_same:
      "\<Gamma> ! j = \<Gamma>2 ! j"
      by (simp add: TyVar.prems(2,3) shift_gt)

    from TyVar.hyps(2) lookup_same
    have lookup2: "\<Gamma>2 ! j = (xs', ty')" by simp

    have j_gt_len_\<Gamma>2: "j < length \<Gamma>2"
    proof -
      from TyVar.hyps(1) len_\<Gamma>1 have "j < length \<Gamma>2 + 1" by simp
      with gt show ?thesis
      using TyVar.prems(2) dual_order.strict_trans1 by blast
    qed

    have "length xs' = length ys" using TyVar.hyps(3) .
    then have "\<Gamma>2 \<turnstile>{P} Graph (Atom (GVar j) ys) : lmap_ty xs' ys ty'"
      by (simp add: TyVar.hyps(4,5,6) j_gt_len_\<Gamma>2 lookup2 typing.TyVar)

    thus ?thesis
      using subst_gt by simp
  qed
next
  case (TyApp \<Gamma> P e1 ty2 ty1 xs e2)
  show ?case
  apply auto
  by (meson TyApp.hyps(2,4) TyApp.prems(1,2,3,4,5) typing.TyApp)

next
  case (TyProd a zs rhs P taus Ts \<Gamma>)
  have P1: "subst_graph i xs g2 (app_prodrule Ts rhs) =
            app_prodrule (map (subst_graph i xs g2) Ts) rhs"
      by (simp add: subst_typrod)

  have P10:
    "\<forall>j < length Ts. \<Gamma>2 \<turnstile>{P} subst i xs g2 (Graph (Ts ! j)) : taus ! j"
    proof (intro allI impI)
      fix j assume Hj: "j < length Ts"

      (* Specialize the big hypothesis TyProd.hyps(4) at j *)
      from TyProd.hyps(4)[rule_format, of j] Hj
      have IHj:
        "\<Gamma> \<turnstile>{P} Graph (Ts ! j) : taus ! j \<and>
         (\<forall>x xa xb xc.
            x \<turnstile>{P} Graph xc : xb \<longrightarrow> xa \<le> length x \<longrightarrow>
            (\<forall>xd. set xd = FL xc \<longrightarrow>
                  set xd = FLty xb \<longrightarrow>
                  \<Gamma> = insert_at x xa (xd, xb) \<longrightarrow>
                  distinct xd \<longrightarrow>
                  x \<turnstile>{P} subst xa xd xc (Graph (Ts ! j)) : taus ! j))"
        by auto

      (* Extract just the substitution part *)
      then have IHj_subst:
        "\<forall>x xa xb xc.
           x \<turnstile>{P} Graph xc : xb \<longrightarrow> xa \<le> length x \<longrightarrow>
           (\<forall>xd. set xd = FL xc \<longrightarrow>
                 set xd = FLty xb \<longrightarrow>
                 \<Gamma> = insert_at x xa (xd, xb) \<longrightarrow>
                 distinct xd \<longrightarrow>
                 x \<turnstile>{P} subst xa xd xc (Graph (Ts ! j)) : taus ! j)"
        by auto

      (* Instantiate with x = Γ2, xa = i, xb = ty2, xc = g2, xd = xs *)
      show "\<Gamma>2 \<turnstile>{P} subst i xs g2 (Graph (Ts ! j)) : taus ! j"
         using Hj TyProd.prems(1,2,3,4,5)
              \<open>j < length Ts \<Longrightarrow> \<Gamma> \<turnstile>{P} Graph (Ts ! j) : taus ! j \<and> (\<forall>x xa xb xc. x \<turnstile>{P} Graph xc : xb \<longrightarrow> xa \<le> length x \<longrightarrow> (\<forall>xd. \<Gamma> = insert_at x xa (xd, xb) \<longrightarrow> set xd = FL xc \<longrightarrow> distinct xd \<longrightarrow> x \<turnstile>{P} subst xa xd xc (Graph (Ts ! j)) : taus ! j))\<close>
    by presburger
    qed

  then show ?case
  apply auto
     using P1 TyProd.hyps(1,2,3,5) typing.TyProd by auto
next
  case (TyCase \<Gamma> P e0 ty1' \<Gamma>2' e1 ty2' e2 T)

  have IHe0: "\<Gamma>2 \<turnstile>{P} subst i xs g2 e0 : ty1'"
    using TyCase.hyps(2) TyCase.prems(1,2,3,4,5) by presburger

  have "\<Gamma>2 \<turnstile>{P} Graph g2 : ty2"
    by (simp add: TyCase.prems(1))
  then have P5: "\<Gamma>2' @ \<Gamma>2 \<turnstile>{P} (lift 0 ^^ length \<Gamma>2') (Graph g2) : ty2"
    by (simp add: weakening_lefts)

  have "i \<le> length \<Gamma>2"
    by (simp add: TyCase.prems(2))
  then have P4: "i + length \<Gamma>2' \<le> length (\<Gamma>2' @ \<Gamma>2)"
    by auto


  have "\<Gamma> = insert_at \<Gamma>2 i (xs, ty2)"
    by (simp add: TyCase.prems(3))
  then have IHe1:
    "\<Gamma>2' @ \<Gamma> = insert_at (\<Gamma>2' @ \<Gamma>2) (i + length \<Gamma>2') (xs, ty2)"
    by (simp add: insert_at_shift)
  then have IHe1B:
    "\<Gamma>2' @ \<Gamma>2 \<turnstile>{P}
    subst (i + length \<Gamma>2') xs ((lift_graph 0 ^^ (length \<Gamma>2')) g2) e1 : ty2'"
   by (metis P4 P5 TyCase.hyps(4) TyCase.prems(4,5) lifts_graph2 lifts_graph_freelinks)

  have IHe2: "\<Gamma>2 \<turnstile>{P} subst i xs g2 e2 : ty2'"
    using TyCase.hyps(6) TyCase.prems(1,2,3,4,5) by presburger

  have T1: "\<Gamma>2 \<turnstile>{P}
    Case (subst i xs g2 e0) \<Gamma>2' T
         (subst (i + length \<Gamma>2') xs ((lift_graph 0 ^^ (length \<Gamma>2')) g2) e1)
	 (subst i xs g2 e2)
    : ty2'"
    using IHe0 IHe1B IHe2 typing.TyCase by blast
  then show ?case
    by simp
qed


subsection \<open>Inversion Lemma\<close>


lemma FL_ty_lmap:
  assumes A1: "FLty ty = set xs"
  assumes A2: "length xs = length ys"
  assumes A3: "distinct xs"
  shows "FLty (lmap_ty xs ys ty) = set ys"
proof (cases ty)
  case (TBase x11 x12)
  then show ?thesis
  apply (simp add: FLty_def)
  using A1 A2 A3 lsubst_zip_image by auto
next
  case (TArrow x21 x22 x23)
  then show ?thesis
  apply (simp add: FLty_def)
  using A1 A2 A3 lsubst_zip_image by auto
qed


lemma FL_typing_LRHS:
  assumes "\<Gamma> \<turnstile>{P} G : ty"
  assumes "G = Graph g"
  shows "FL g = FLty ty"
using assms
proof (induction arbitrary: g set: typing)
  case (TyVar i \<Gamma> xs ty ys P)
  then show ?case
  using FL_ty_lmap by force
next
  case (TyArrow xs ty1 \<Gamma> P e ty2 ys)
  then show ?case
  apply auto
  done
next
  case (TyApp \<Gamma> P e1 ty2 ty1 xs e2)
  then show ?case
  apply auto
  done
next
  case (TyProd a xs rhs P taus Ts \<Gamma>)
  have"\<forall>i < length Ts. FLty (taus_of_rhs rhs ! i) = FL (Ts ! i)"
     by (simp add: TyProd.IH TyProd.hyps(2))
  then have P2: "map FLty (taus_of_rhs rhs) = map FL Ts"
    using TyProd.hyps(2,3) map_equality_iff by blast
  then show ?case
  apply auto
   using TyProd.hyps(4) TyProd.prems app_prodrule_FL_equiv apply blast
   using TyProd.hyps(4) TyProd.prems app_prodrule_FL_equiv by blast
next
  case (TyCong \<Gamma> P g1 ty g2)
  then show ?case
  apply simp
  by (simp add: freelinks_equiv)
next
  case (TyAlpha \<Gamma>2 P g ty xs ys)
  then show ?case
  by (metis (mono_tags, lifting) FL_ty_lmap exp.inject(1) lsubst_graph_freelinks)
next
  case (TyCase \<Gamma> P e0 ty1 \<Gamma>2 e1 ty2 e2 T)
  then show ?case
  by auto
qed


lemma typing_inv_graph_abs_aux:
  assumes T: "\<Gamma> \<turnstile>{P} e' : ty"
  assumes ty: "ty = TArrow ty1 ty2 zs"
      and E: "e' = Graph g'"
      and C: "g' \<simeq> Atom (GAbs xs ty3 e) ys"
  shows "(xs, ty1) # \<Gamma> \<turnstile>{P} e : ty2"
using assms
proof (induction arbitrary: xs ty1 ty2 zs e ys g' rule: typing.induct)
  case (TyVar i \<Gamma> xs ty ys P)
  then show ?case
  apply auto
  by (simp add: abs_var_cong_inv)
next
  case (TyArrow xs' ty1' \<Gamma> P e2' ty2' ys')
  then show ?case
  by (metis abs_cong_inv exp.inject(1) type.inject(2)) 
next
  case (TyApp \<Gamma> P e1 ty1 ty2 xs e2)
  then show ?case
  apply auto
  done
next
  case (TyProd a xs rhs P taus Ts \<Gamma>)
  then show ?case
  apply auto
  done
next
  case (TyCong \<Gamma> P e1 ty e2)
  then show ?case
  apply simp
  by (meson gcong.trans)
next
  case (TyAlpha \<Gamma>2' P g ty' xs' ys')
  (* link α-conversion does not change the fact “g is an abstraction atom up to gcong” *)
  have P1: "set xs' = FL g"
    using TyAlpha.hyps(2) by fastforce
  have P2: "set ys' = FL (lmap (lsubst (zip xs' ys')) g)"
    by (simp add: P1 TyAlpha.hyps(3,4) lsubst_graph_freelinks)
  have P3: "lmap (lsubst (zip xs' ys')) g \<simeq> Atom (GAbs xs ty3 e) ys"
    using TyAlpha.prems(2,3) by blast
  then have P4: "FL (lmap (lsubst (zip xs' ys')) g) = FL (Atom (GAbs xs ty3 e) ys)"
    by (simp add: freelinks_equiv)
  then have P7: "set ys' = set ys"
    by (simp add: P2)

  then have P8: "distinct xs'"
    by (simp add: TyAlpha.hyps(4))
  then have P9: "distinct ys'"
    by (simp add: TyAlpha.hyps(5))

  have P6: "lmap (lsubst (zip ys' xs')) (lmap (lsubst (zip xs' ys')) g) \<simeq>
            lmap (lsubst (zip ys' xs')) (Atom (GAbs xs ty3 e) ys)"
      using P3 lmap_graph_cong by blast
  have P7: "lmap (lsubst (zip ys' xs')) (lmap (lsubst (zip xs' ys')) g) = g"
     by (metis P1 P8 P9 TyAlpha.hyps(3) dual_order.refl lmap_lsubst_inv_inv map_fst_zip map_snd_zip
         zip_commute)
  have P8: "g \<simeq> lmap (lsubst (zip ys' xs')) (Atom (GAbs xs ty3 e) ys)"
     using P6 P7 by auto
  then have P9: "g \<simeq> Atom (GAbs xs ty3 e) (map (lsubst (zip ys' xs')) ys)"
     by simp


  have P14: "FLty ty' = FL g"
     using FL_typing_LRHS TyAlpha.hyps(1) by presburger
  then have P15: "FLty ty' = set xs'"
     by (simp add: P1)

  have P10: "lmap_ty xs' ys' ty' = TArrow ty1 ty2 zs"
     by (simp add: TyAlpha.prems(1))
  have P12: "lmap_ty ys' xs' (lmap_ty xs' ys' ty') = lmap_ty ys' xs' (TArrow ty1 ty2 zs)"
     using P10 by presburger
  have P13: "ty' = lmap_ty ys' xs' (TArrow ty1 ty2 zs)"
     by (metis P10 P15 TyAlpha.hyps(3,4,5) dual_order.refl lmap_ty_inv_inv)
  then have P16: "ty' = TArrow ty1 ty2 (map (lsubst (zip ys' xs')) zs)"
     by auto

  show ?case
    using P16 P9 TyAlpha.IH by blast
next
  case (TyCase \<Gamma> P e0 ty1 \<Gamma>2 e1 ty2 e2 T)
  then show ?case
  by auto
qed


corollary typing_inv_graph_abs:
  assumes T: "\<Gamma> \<turnstile>{P} Graph (Atom (GAbs xs ty3 e) ys) : TArrow ty1 ty2 zs"
  shows "(xs, ty1) # \<Gamma> \<turnstile>{P} e : ty2"
by (meson assms gcong.refl typing_inv_graph_abs_aux)



subsection \<open>Subject Reduction\<close>


text \<open>
  Subject reduction:
  If a term e reduces to e' by a call-by-value step,
  and e is well-typed,
  then e' is also well-typed with the same type.
  This ensures that evaluation preserves typing.
\<close>
lemma weakening_right:
  assumes "\<Gamma> \<turnstile>{P} e : \<tau>"
  shows "\<Gamma>@\<Gamma>2 \<turnstile>{P} e : \<tau>"
using assms
proof (induct set: typing)
  case (TyVar i \<Gamma> xs ty ys P)
  then show ?case
  by (simp add: nth_append_left typing.TyVar)
next
  case (TyArrow xs ty1 \<Gamma> P e ty2 ys)
  then show ?case
  by (simp add: typing.TyArrow)
next
  case (TyApp \<Gamma> P e1 ty1 ty2 xs e2)
  then show ?case
  by (simp add: typing.TyApp)
next
  case (TyProd a xs rhs P taus Ts \<Gamma>)
  then show ?case
  by (simp add: typing.TyProd)
next
  case (TyCong \<Gamma> P g1 ty g2)
  then show ?case
  using typing.TyCong by presburger
next
  case (TyAlpha \<Gamma>2 P g ty xs ys)
  then show ?case
  by (simp add: typing.TyAlpha)
next
  case (TyCase \<Gamma> P e0 ty1 \<Gamma>2 e1 ty2 e2 T)
  then show ?case
  by (simp add: typing.TyCase)
qed


lemma substs_lemma0:
  assumes A1: "(xs, ty) # \<Gamma>1 \<turnstile>{P} e1 : ty1"
  assumes A2: "distinct xs"
  assumes A3: "FL g = set xs"
  assumes A4: "[] \<turnstile>{P} (Graph g) : ty"
  shows "\<Gamma>1 \<turnstile>{P} subst 0 xs g e1 : ty1"
proof -
  have P1: "\<Gamma>1 \<turnstile>{P} Graph g : ty"
    by (metis A4 append_Nil weakening_right)
  then show ?thesis
    using A1 A2 A3 A4 subst_lemma by auto
qed


lemma substs_lemma_aux:
  assumes A1: "\<Gamma> = map fst XsGs"
  assumes A2: "\<Gamma> @ \<Gamma>1 \<turnstile>{P} e1 : ty1"
  assumes A3: "\<forall>((xs, ty), g) \<in> set XsGs. (
               distinct xs \<and> FL g = set xs \<and>
               [] \<turnstile>{P} Graph g : ty)"
  shows "\<Gamma>1 \<turnstile>{P} substs XsGs e1 : ty1"
using assms
proof (induct XsGs arbitrary: \<Gamma> \<Gamma>1 e1 ty1)
  case Nil
  then show ?case
  by (simp add: substs)
next
  case (Cons a \<Gamma>)
  then show ?case
  apply (simp add: substs)
  using substs_lemma0 by force
qed


lemma substs_lemma:
  assumes A1: "\<Gamma> @ \<Gamma>1 \<turnstile>{P} e1 : ty1"
  assumes A2: "length \<Gamma> = length gs"
  assumes A3: "XsGs = zip \<Gamma> gs"
  assumes A4: "\<forall>((xs, ty), g) \<in> set XsGs. (
               distinct xs \<and> FL g = set xs \<and>
               [] \<turnstile>{P} Graph g : ty)"
  shows "\<Gamma>1 \<turnstile>{P} substs XsGs e1 : ty1"
using substs_lemma_aux apply auto
using A1 A2 A3 A4 map_fst_zip split_beta by auto


text \<open>
  Subject reduction:
  If a term e reduces to e' by a call-by-value step,
  and e is well-typed,
  then e' is also well-typed with the same type.
  This ensures that evaluation preserves typing.
\<close>
lemma subject_reduction:
  assumes "\<Gamma> \<turnstile>{P} e : \<tau>"
      and "e ->{P} e'"
    shows "\<Gamma> \<turnstile>{P} e' : \<tau>"
using assms
proof (induct arbitrary: e' set: typing)
  case (TyVar i \<Gamma> xs ty ys P)
  then show ?case
  apply auto
  done
next
  case (TyArrow xs ty1 \<Gamma> P e ty2 ys)
  then show ?case
  apply auto
  done
next
  case (TyApp \<Gamma> P e1 ty1 ty2 zs e2)
  (* From the typing rule: *)
  note T_fun = TyApp.hyps(1)   (* Γ ⊢P e1 : TArrow ty2 ty1 xs *)
  have "\<Gamma> \<turnstile>{P} e1 : TArrow ty1 ty2 zs"
    by (simp add: T_fun)

  note T_arg = TyApp.hyps(3)   (* Γ ⊢P e2 : ty2 *)
  have "\<Gamma> \<turnstile>{P} e2 : ty1"
    by (simp add: T_arg)

  (* Induction hypotheses: *)
  note IH_fun = TyApp.hyps(2)    (* ∀e'. e1 ->{P} e' ⟹ Γ ⊢P e' : TArrow ty2 ty1 xs *)
  note IH_arg = TyApp.hyps(4)    (* ∀e'. e2 ->{P} e' ⟹ Γ ⊢P e' : ty2      *)
  note Step  = TyApp.prems     (* e1 · e2 ->{P} e' *)

  show ?case
  proof (cases rule: cbv_ty_AppE[OF Step])
    case (1 v xs lam ty e ys)

    have P1: "(xs, ty1) # \<Gamma> \<turnstile>{P} e : ty2 ==>
     \<Gamma> \<turnstile>{P} Graph (Atom (GAbs xs ty1 e) ys) : TArrow ty1 ty2 ys"
      using "1"(3,4,7) FL_typing_LRHS T_arg TyArrow by auto

    have P2: "\<Gamma> \<turnstile>{P} Graph (Atom (GAbs xs ty e) ys) : TArrow ty1 ty2 zs"
      using "1"(5) T_fun
      by (metis "1"(6) TyCong)
    have P3: "(xs, ty1) # \<Gamma> \<turnstile>{P} e : ty2"
      using P2 typing_inv_graph_abs by auto
    then show ?thesis
      using "1"(1,3,4,7) T_arg subst_lemma by force
  next
    case (2 e1')
    then show ?thesis
    apply auto
    using IH_fun T_arg typing.TyApp by blast
  next
    case (3 e')
    then show ?thesis
    apply auto
    using IH_arg T_fun typing.TyApp by blast
  qed
next
  case (TyProd a xs rhs P taus Ts \<Gamma>)
  then show ?case
  apply auto
  done
next
  case (TyCong \<Gamma> P g1 ty g2)
  then show ?case
  by auto
next
  case (TyAlpha \<Gamma>2 P g ty xs ys)
  then show ?case
  apply auto
  done
next
  case (TyCase \<Gamma> P e0' ty1' \<Gamma>2' e1' ty2' e2' T)

  note Step  = TyCase.prems     (* e1 · e2 ->{P} e' *)

  have P1: "\<Gamma> \<turnstile>{P} e0' : ty1'"
    by (simp add: TyCase.hyps(1))
  have P3: "\<Gamma>2' @ \<Gamma> \<turnstile>{P} e1' : ty2'"
    by (simp add: TyCase.hyps(3))
  have P5: "\<Gamma> \<turnstile>{P} e2' : ty2'"
    by (simp add: TyCase.hyps(5))
  have P7: "Case e0' \<Gamma>2' T e1' e2' ->{P} e'"
    by (simp add: Step)

  show ?case
  proof (cases rule: cbv_ty_CaseE[OF Step])
    case (1 v XsGs)
    then show ?thesis
      using P3 substs_lemma by presburger
  next
    case (2 v)
    then show ?thesis
    apply auto
      using P5 by blast
  next
    case (3 e0')
    then show ?thesis
    apply auto
      using P3 P5 TyCase.hyps(2) typing.TyCase by blast
  qed
qed


text \<open>
  Multi-step subject reduction:
  If e reduces to e' in zero or more steps,
  then e' has the same type as e.
\<close>
corollary subject_reduction':
  assumes "e ->{P}* e'"
   and "\<Gamma> \<turnstile>{P} e : \<tau>"
  shows "\<Gamma> \<turnstile>{P} e' : \<tau>"
using assms
  by (induct set: rtranclp) (iprover intro: subject_reduction)+



subsection \<open>Canonical\<close>


lemma canonical_forms_arrow:
  assumes T: "\<Gamma> \<turnstile>{P} v : ty"
  assumes V: "is_val v"
  assumes A3: "\<Gamma> = []"
  assumes A4: "ty = TArrow ty1 ty2 zs"
  shows "\<exists>xs e' ys g. 
    (v = Graph g \<and> 
     g \<simeq> Atom (GAbs xs ty1 e') ys \<and> 
     distinct xs \<and>
     set xs = FLty ty1)"
using assms
proof (induct arbitrary: zs set: typing)
  case (TyVar i \<Gamma> xs ty ys P)
  then show ?case
  apply auto
  done
next
  case (TyArrow xs ty1 \<Gamma> P e ty2 ys)
  then show ?case
  by auto
next
  case (TyApp \<Gamma> P e1 ty1 ty2 xs e2)
  then show ?case
  apply auto
  done
next
  case (TyProd a xs rhs P taus Ts \<Gamma>)
  then show ?case
  apply auto
  done
next
  case (TyCong \<Gamma> P g1 ty g2)
  show ?case
  apply auto
  by (metis TyCong.hyps(2,3) TyCong.prems(1,2,3) cong_is_val exp.inject(1) gcong.sym gcong.trans) 
next
  case (TyAlpha \<Gamma>2 P g ty xs ys)
  have P1: "is_val (Graph g)"
    using TyAlpha.prems(1) is_graph_val_ignore_lmap is_val.simps(1) by blast
  then show ?case
  apply auto
  by (metis (no_types, lifting) FL_typing_LRHS P1 TyAlpha.hyps(1,2,3,4,5,6) TyAlpha.prems(2,3) dual_order.refl
    exp.inject(1) lmap.simps(2) lmap_graph_cong lmap_ty.simps(2) lmap_ty_inv_inv)
next
  case (TyCase \<Gamma> P e0 ty1 \<Gamma>2 e1 ty2 e2 T)
  then show ?case
  apply auto
  done
qed


subsection \<open>Progress\<close>


lemma Nus_is_val:
  "is_graph_val g = is_graph_val (Nus1 i g)"
apply (induct i arbitrary: g)
by auto


lemma Mols1_is_val:
  "(is_graph_val g \<and> (\<forall>g \<in> set gs. is_graph_val g)) = is_graph_val (Mols1 g gs)"
proof (induct gs arbitrary: g)
  case Nil
  then show ?case
  apply auto
  apply (simp_all add: Mols1)
  done
next
  case (Cons a gs)
  then show ?case
  apply (simp_all add: Mols1)
  by (metis is_graph_val.simps(4))
qed


lemma fusions_is_val:
  "\<forall>fus \<in> set (fusions_of fs). is_graph_val fus"
apply (simp add: fusions_of_def)
by auto


lemma app_prodrule_is_val:
  assumes A1: "\<forall>i<length Ts. is_val (Graph (Ts ! i))"
  shows "is_graph_val (app_prodrule Ts rhs)"
proof -
  have P0: "\<forall>T \<in> set Ts. is_graph_val T"
    by (metis assms in_set_conv_nth is_val.simps(1))

  obtain i C zs fusions taus where
    prod_rhs: "rhs = (i, (C, zs), fusions, taus)"
  by (metis prod.collapse)

  have "is_graph_val (Atom (GConstr C) zs)"
    by simp

  then have "is_graph_val (Mols1 (Atom (GConstr C) zs) (fusions_of fusions))"
    using Mols1_is_val fusions_is_val by blast

  then have "is_graph_val (Mols1 (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) Ts)"
    using Mols1_is_val P0 by blast

  then have "is_graph_val (Nus1 i (Mols1 (Mols1 (Atom (GConstr C) zs) (fusions_of fusions)) Ts))"
    using Nus_is_val by blast

  then show ?thesis
    apply (simp add: app_prodrule_def)
    using prod_rhs by auto
qed


text \<open>
  Progress: closed, well-typed terms are values or can step.
\<close>
lemma progress:
assumes A1: "\<Gamma> \<turnstile>{P} e : ty"
assumes A2: "\<Gamma> = []"
shows "is_val e \<or> (\<exists>e'. e ->{P} e')"
using assms
proof (induction arbitrary: ty e' set: typing)
  case (TyVar i \<Gamma> xs ty ys P)
  then show ?case
  apply auto
  done
next
  case (TyArrow xs ty1 \<Gamma> P e ty2 ys)
  then show ?case
  apply auto
  done
next
  case (TyApp \<Gamma> P e1 ty1 ty2 xs e2)
  have P1: "is_val e1 \<or> (\<exists>a. e1 ->{P} a)"
    by (simp add: TyApp.IH(1) TyApp.prems)
  have P2: "is_val e2 \<or> (\<exists>a. e2 ->{P} a)"
    by (simp add: TyApp.IH(2) TyApp.prems)

  have Step:
    "(is_val e1 \<and> is_val e2) \<or>
     (\<exists>a. e1 ->{P} a) \<or> (\<exists>a. e2 ->{P} a)"
  using P1 P2 by blast

  from Step show ?case
  proof (elim disjE)
    assume VV: "is_val e1 \<and> is_val e2"
    then have V1: "is_val e1" and V2: "is_val e2" by auto

    from V1 obtain g1 where E1: "e1 = Graph g1"
      by (cases e1) auto
    from V2 obtain g2 where E2: "e2 = Graph g2"
      by (cases e2) auto

    have P3C:
      "\<exists>xs e' ys. g1 \<simeq> Atom (GAbs xs ty1 e') ys \<and> set xs = FLty ty1 \<and> distinct xs"
     by (metis E1 TyApp.hyps(1) TyApp.prems V1 exp.inject(1) canonical_forms_arrow)

    then show ?case
      by (metis E1 E2 FL_typing_LRHS TyApp.hyps(2) V2 beta_v_ty is_val.simps(1))
  next
    assume S: "(\<exists>a. e1 ->{P} a)"
    then show ?case
    by force
  next
    assume S: "(\<exists>a. e2 ->{P} a)"
    then show ?case
    using P1 by blast
  qed
next
  case (TyProd a xs rhs P taus Ts \<Gamma>)
  have P1: "\<forall>i<length Ts. is_val (Graph (Ts ! i))"
    by (meson TyProd.IH TyProd.prems cbv_ty_GraphE)
  then show ?case
  apply auto
  by (simp add: app_prodrule_is_val)
next
  case (TyCong \<Gamma> P e1 ty e2)
  then show ?case
  by (metis cbv_ty_GraphE cong_is_val)
next
  case (TyAlpha \<Gamma>2 P g ty xs ys)
  then show ?case
  by (metis cbv_ty_GraphE is_graph_val_ignore_lmap is_val.simps(1))
next
  case (TyCase \<Gamma> P e0 ty1 \<Gamma>2 e1 ty2 e2 T)
  then show ?case
  apply auto
  apply (metis cbv_ty.intros(3) exp.exhaust is_val.simps(1,2,3))
  by (metis cbv_ty.intros(3) exp.exhaust is_val.simps(1,2,3))
qed


text \<open>
  Progress: a simpler corollary.
\<close>
corollary progress':
  assumes "[] \<turnstile>{P} e : \<tau>"
  shows "is_val e \<or> (\<exists>e'. e ->{P} e')"
using assms progress by auto


subsection \<open>Soundness\<close>


text \<open>
  Type soundness theorem:
  If a closed term is well-typed and reduces (in zero or more steps)
  to some term e', then e' is either a value or can take a further step.
  This combines subject reduction and progress to establish
  the standard type soundness property of the language.
\<close>
theorem type_soundness:
  assumes WT: "[] \<turnstile>{P} e : \<tau>"
      and STEPS: "e ->{P}* e'"
  shows "is_val e' \<or> (\<exists>u. e' ->{P} u)"
proof -
  have "[] \<turnstile>{P} e' : \<tau>" using STEPS WT subject_reduction' by blast
  thus ?thesis using progress' by blast
qed


end



section\<open>Introduction\<close>

text \<open>
This is a proof for the soundness of the type system of the $\lambda_{GT}$ language.
\<close>


theory LambdaGT_LI
imports
  Main
  "HOL-Library.Multiset"
  "HOL-Library.FSet"
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
given by mutually recursive datatypes.
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
| "lmap f (Atom p xs) = Atom p (map f xs)"
| "lmap f (Fusion  x y) = Fusion (f x) (f y)"
| "lmap f (Mol g1 g2) = Mol (lmap f g1) (lmap f g2)"
| "lmap f (Nu g) = Nu (lmap (\<lambda>x. if x = 0 then x else (f (x - 1) + 1)) g)"


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
We first define the congruence relation over graphs
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
  "insert_at xs       0       x = x # xs"
| "insert_at []       (Suc n) x = [x]"
| "insert_at (y # ys) (Suc n) x = y # insert_at ys n x"


text \<open>Types and Typing Rules\<close>


text \<open>
Simple types:
\<^item> \<open>TBase n xs\<close> : base type identified by \<open>n\<close> with free links \<open>xs\<close>
\<^item> \<open>TArrow ty1 ty2 xs\<close> : function type \<open>ty1 => ty2\<close> with free links \<open>xs\<close>.
\<^item> \<open>TLI tys ty xs\<close> : linear implication type with hided links \<open>xs\<close>.
\<close>
datatype type =
  TBase nat links
| TArrow type type links
| TLI "(type multiset)" nat links "link fset"


text \<open>
Typing environments map de Bruijn indices to (links, type) pairs.
The head is the most recently bound variable.
Normally: var -> var
This: var, links -> var, links.
Thus: links -> type.
\<close>
type_synonym tyenv = "(links * type) list"

text \<open>Right-hand side of a production rule.\<close>
type_synonym prodrule_RHS =
  "nat * (string * links) * (link * link) list * type list"

text \<open>Whole production rule: left-hand side tag / links and RHS.\<close>
type_synonym prodrule =
  "(nat * links) * prodrule_RHS"


text \<open>A set of the free links of a type.\<close>
(* 線型含意型の内部にしか出現しない自由リンクは含まれない． *)
primrec FLty :: "type => link set" where
  "FLty (TBase i xs) = set xs"
| "FLty (TArrow ty1 ty2 xs) = set xs"
| "FLty (TLI tys a xs ys) = fset ys"


text \<open>A set of the all the free links of a type.\<close>
(* 線型含意型の内部にしか出現しない自由リンクも含まれる． *)
primrec ALty :: "type => link set" where
  "ALty (TBase i xs) = set xs"
| "ALty (TArrow ty1 ty2 xs) = set xs"
| "ALty (TLI tys a xs ys) = \<Union> (set_mset (image_mset ALty tys)) \<union> set xs \<union> fset ys"
(* ys を入れるべきかは後でゆっくり考えた方が良いかも知れない． *)


lemma FLty_subset_ALty:
  "FLty ty \<subseteq> ALty ty"
apply (induct ty) by auto


lemma finite_FLty:
  "finite (FLty ty)"
apply (induct ty) by auto

lemma finite_ALty:
  "finite (ALty ty)"
apply (induct ty) by auto


(* Fusion の自由リンクの集合を返す． *)
definition FLfusion_set :: "(link * link) list => link set" where
  "FLfusion_set fusions == \<Union> (x,y) \<in> set fusions. {x, y}"


(* Fusion の自由リンクの有限集合を返す． *)
definition FLfusion_fset :: "(link * link) list => link fset" where
  "FLfusion_fset fusions == Abs_fset (\<Union> (x,y) \<in> set fusions. {x, y})"


lemma finite_FLfusion_set:
  "finite (FLfusion_set fusions)"
apply (simp add: FLfusion_set_def)
by fastforce


(* Fusion の自由リンクのリストを返す．
集合を返す FLfusion_set だけあれば良いような気はするが，これはこれで利用している．
*)
definition FLfusion :: "(link * link) list => links" where
  "FLfusion fusions ==
     foldr (\<lambda>(x,y) acc. [x,y] @ acc) fusions []"



(* Fusion それぞれの自由リンクを取得してから集合にまとめるのが，
Fusion のリストからそれらの自由リンクを取得すると同じということ．
*)
lemma fusions_freelinks_equiv2B:
  "set (FLfusion fusions) = FLfusion_set fusions"
proof (induction fusions)
  case Nil
  then show ?case
    by (simp add: FLfusion_def FLfusion_set_def)
next
  case (Cons a fusions)
  obtain x y where a_def: "a = (x,y)"
    by (cases a)

  have rhs_step:
    "FLfusion_set (a # fusions) = {x,y} \<union> FLfusion_set fusions"
    unfolding FLfusion_set_def a_def
    by auto

  from Cons.IH
  have "set (foldr (\<lambda>(x,y) acc. [x,y] @ acc) fusions []) = FLfusion_set fusions"
    unfolding FLfusion_def by simp

  with step rhs_step
  show ?case
    unfolding FLfusion_def
    using a_def by auto
qed



text \<open>
Free links of RHS on production rules:
we shift by \<open>i\<close> to account for the \<open>Nus1 i\<close> binder.
\<close>
definition FLrhs :: "prodrule_RHS => link set" where
  "FLrhs rhs ==
   (case rhs of (i, (C, zs), fusions, taus) =>
     {n. n + i \<in> set zs \<union> FLfusion_set fusions \<union> (\<Union> (FLty ` set taus))})"


(*
(* リンク代入において domain に restriction するもの．
不要になったのでコメントアウトしている．
*)
text \<open>
Free-link function limitation on link substitution on types.
\<close>
definition lflim :: "links => (link => link) => (link => link)" where
  "lflim xs f = (\<lambda> x. if x \<in> set xs then f x else x)"
*)


(* 線型含意型のリンク代入において，
線型含意型の外部自由リンク以外のリンク代入も認めていることに注意． *)
text \<open>
Free-link substitution on types.
\<close>
primrec lmap_ty :: "(link => link) => type => type" where
  "lmap_ty f (TBase i zs) =
     TBase i (map f zs)"
| "lmap_ty f (TArrow ty1 ty2 zs) =
     TArrow ty1 ty2 (map f zs)"
| "lmap_ty f (TLI tys a xs ys) =
     TLI (image_mset (lmap_ty f) tys) a (map f xs) (f |`| ys)"
     (* 単に f を再帰的に適用しているだけで，特に domain restriction はかけていない． *)


text \<open>
Free-link substitution on types.
Note: this substitutes only free links.
\<close>
(* リンク列を得て，リンク代入を行う． *)
definition lsubst_ty :: "links => links => type => type" where
  "lsubst_ty xs ys ty = lmap_ty (lsubst (zip xs ys)) ty"


(* ここから生成規則からのグラフの組み立て用の関数の定義． *)

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


(* ここから線型含意型の組み立て用の関数の定義． *)

text \<open>
Make linear implication type when the application of TyLIIntro.
\<close>
(* 生成規則から constructor atom と fusions からなるグラフを生成する． *)
definition make_diffgraph ::
  "prodrule_RHS => type graph" where
  "make_diffgraph rhs =
     (case rhs of (i, (C, zs), fusions, taus) =>
        Mols1 (Atom (GConstr C) zs) (fusions_of fusions))"



text \<open>
Make graph when application of TyLIIntro.
\<close>
(* 生成規則から Ty-LI-Intro を適用した際の線型含意型を生成する． *)
definition make_LI ::
  "prodrule => type" where
  "make_LI prodrule =
     (case prodrule of ((a, xs), (i, (C, zs), fusions, taus)) =>
        TLI (mset taus) a xs (fset_of_list zs |\<union>| FLfusion_fset fusions))"


(* ここから TyLIIntro の両辺において自由リンクが等しいという証明を行う． *)


lemma FL_Mols1_decomp:
  "FL (Mols1 a bs) = FL a \<union> \<Union> (FL ` set bs)"
proof (induct bs arbitrary: a)
  case Nil
  then show ?case
  apply (simp_all add: Mols1)
  done
next
  case (Cons a bs)
  then show ?case
  apply (simp_all add: Mols1)
  apply auto
  done
qed

lemma FLfusion_set_equiv:
  "FLfusion_set fusions = \<Union> (FL ` set (fusions_of fusions))"
proof (induct fusions)
  case Nil
  then show ?case
  apply auto
  apply (simp_all add: Mols1 FLfusion_set_def fusions_of_def)
  done
next
  case (Cons a fusions)
  then show ?case
  apply auto
  apply (simp_all add: Mols1 FLfusion_set_def fusions_of_def)
  apply (simp add: case_prod_beta)
  by fastforce
qed


lemma FLfusion_fset_set_equiv:
  "fset (FLfusion_fset fusions) = FLfusion_set fusions"
apply (simp_all add: FLfusion_fset_def FLfusion_set_def)
proof (induct fusions)
  case Nil
  then show ?case
  apply auto
  using bot_fset.abs_eq by force
next
  case (Cons a fusions)
  then show ?case
  by (metis FLfusion_set_def fset_inverse fset_of_list.rep_eq
    fusions_freelinks_equiv2B)
qed


(* これは使っている． *)
lemma FLfusion_fset_equiv:
  "fset (FLfusion_fset fusions) = \<Union> (FL ` set (fusions_of fusions))"
apply (simp_all add: FLfusion_fset_def fusions_of_def)
proof (induct fusions)
  case Nil
  then show ?case
  apply auto
  using bot_fset_def by force
next
  case (Cons a fusions)
  then show ?case
  by (metis (mono_tags, lifting) FL.simps(3) FLfusion_fset_def
    FLfusion_fset_set_equiv FLfusion_set_def Sup.SUP_cong
    case_prod_beta)
qed


(* Ty-LI-Intro を適用時に，型付け関係の両辺の自由リンク集合が等しいということ．*)
lemma TyLIIntro_freelinks_equiv:
  assumes "rhs = (i, (C, zs), fusions, taus)"
  assumes "prodrule = ((a, xs), rhs)"
  shows "FLty (make_LI prodrule) = FL (make_diffgraph rhs)"
apply (simp_all add: make_diffgraph_def make_LI_def FLty_def)
apply (simp_all add: FL_Mols1_decomp assms)
using FLfusion_fset_equiv
by (simp add: fset_of_list.rep_eq)



(* Ty-Elim0 で binder を補うために利用している． *)
text \<open>
Bind free link in a graph.
\<close>
definition lbind :: "link => 'ty graph => 'ty graph" where
  "lbind x g = Nu ((lmap (\<lambda>y. if y = Suc x then 0 else y)) (lmap Suc g))"

text \<open>
Bind free links in a graph.
\<close>
definition lbinds :: "links => 'ty graph => 'ty graph" where
  "lbinds xs g = fold lbind xs g"


text \<open>
Typing rules.
\<close>
inductive typing ::
  "tyenv => prodrule list => type exp => type => bool"
  (\<open>_ \<turnstile>{_} _ : _\<close> [50, 50, 50, 50] 50)
where
  TyVar:
    "i < length \<Gamma> ==>
     xs = map fst s ==>
     ys = map snd s ==>
     \<Gamma> ! i = (xs, ty) ==>
     distinct xs ==>
     distinct ys ==>
     set xs = FLty ty ==>
     set ys \<inter> ALty ty - FLty ty = {} ==>
     \<Gamma> \<turnstile>{P} Graph (Atom (GVar i) ys) : lmap_ty (lsubst s) ty"
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
     set xs = ALty ty ==>
     length xs = length ys ==>
     distinct xs ==>
     distinct ys ==>
     FL g \<subseteq> set xs ==>
     \<Gamma>2 \<turnstile>{P} Graph (lmap (lsubst (zip xs ys)) g)
       : lsubst_ty xs ys ty"
| TyCase:
    "\<Gamma> \<turnstile>{P} e0 : ty1 ==>
     \<Gamma>2 @ \<Gamma> \<turnstile>{P} e1 : ty2 ==>
     \<Gamma> \<turnstile>{P} e2 : ty2 ==>
     \<Gamma> \<turnstile>{P} Case e0 \<Gamma>2 T e1 e2 : ty2"
| TyLIIntro:
    "(lhs, rhs) \<in> set P ==>
     \<Gamma> \<turnstile>{P} Graph (make_diffgraph rhs) : make_LI (lhs, rhs)"
| TyLITrans:
    "\<Gamma> \<turnstile>{P} Graph T1 : TLI ({#TBase a2 xs2#} + tys1) a1 xs1 ys1 ==>
     \<Gamma> \<turnstile>{P} Graph T2 : TLI tys2 a1 xs2 ys2 ==>
     ys = (ys1 |\<union>| ys2) ==>
     \<Gamma> \<turnstile>{P} Graph (Mol T1 T2) : TLI (tys1 + tys2) a1 xs2 ys"
| TyLIElim0:
    "ys = fset_of_list ys' ==>
     set xs \<subseteq> FL T ==>
     \<Gamma> \<turnstile>{P} Graph T : TLI 0 a xs ys ==>
     \<Gamma> \<turnstile>{P} Graph (lbinds (filter (\<lambda>y. y \<notin> set xs) ys') T)
       : TBase a xs"
| TyLIIntro0:
    "\<Gamma> \<turnstile>{P} Graph T : TBase a xs ==>
     \<Gamma> \<turnstile>{P} Graph T : TLI 0 a xs (fset_of_list xs)"


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


lemma FL_Nu_lmap_Suc:
  "FL g = FL (Nu (lmap Suc g))"
by (simp add: FL_lmap_deSuc_Suc)


lemma lbind_hide:
  "FL (lbind x g) = FL g - {x}"
apply (simp add: lbind_def)
apply auto
apply (simp_all add: FL_lmap_commute image_iff)
done


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


lemma lsubst_ignore:
  assumes "y \<notin> set (map fst xs)"
  shows "lsubst xs y = y"
using assms
proof (induct xs)
  case Nil
  then show ?case
  by simp
next
  case (Cons a xs)
  then show ?case
  by (simp add: lsubst_simp)
qed


lemma lsubst_inv_invB:
  assumes "y \<notin> set (map fst xs)"
  assumes "y \<notin> set (map snd xs)"
  shows "lsubst (swap_list xs) (lsubst xs y) = y"
proof -
  have "lsubst (swap_list xs) (lsubst xs y) = lsubst (swap_list xs) y"
    using assms(1) lsubst_ignore by presburger
  also have "... = y"
    proof -
      have "y \<notin> set (map fst (swap_list xs))"
        by (metis assms(2) swap_map_fst)
      then show ?thesis
        using lsubst_ignore by presburger
    qed
  finally show ?thesis .
qed


lemma lsubst_inv_invC:
  assumes "distinct (map snd xs)"
  assumes "y \<notin> set (map fst xs) --> y \<notin> set (map snd xs)"
  shows "lsubst (swap_list xs) (lsubst xs y) = y"
by (metis assms(1,2) lsubst_inv_inv lsubst_inv_invB swap_map_fst swap_swap_list)


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


(* リンク代入の domain に自由リンクにないものがあっても，それを省いたものと同じになる．
ということを証明している．
*)


lemma lsubst_ignore_befores:
  assumes "xs = ys1 @ ys2"
  assumes "z \<notin> set (map fst ys1)"
  shows "lsubst xs z = lsubst ys2 z"
using assms
proof (induct ys1 arbitrary: ys2 xs)
  case Nil
  then show ?case
  apply auto
  done
next
  case (Cons a ys1)
  then show ?case
  apply auto
  using lsubst_simp by presburger
qed

lemma lsubst_ignore_afters:
  assumes "xs = ys1 @ ys2"
  assumes "z \<notin> set (map fst ys2)"
  shows "lsubst xs z = lsubst ys1 z"
using assms
proof (induct ys1 arbitrary: ys2 xs)
  case Nil
  then show ?case
  apply auto
  by (simp add: lsubst_ignore)
next
  case (Cons a ys1)
  then show ?case
  apply auto
  using lsubst_simp by presburger
qed


corollary lsubst_ignore_beforeafters:
  assumes "xs = ys1 @ ys2 @ ys3"
  assumes "z \<notin> set (map fst ys1)"
  assumes "z \<notin> set (map fst ys3)"
  shows "lsubst xs z = lsubst ys2 z"
  using assms(1,2,3) lsubst_ignore_afters lsubst_ignore_befores by presburger


lemma lsubst_lemma1:
  assumes "xs = ys1 @ [(k, v)] @ ys3"
  assumes "distinct (map fst xs)"
  assumes "z = k"
  shows "z \<notin> set (map fst ys1)"
  and "z \<notin> set (map fst ys3)"
apply auto
using assms
apply (metis Un_iff append_Cons distinct_append distinct_map eq_key_imp_eq_value in_set_conv_decomp
    not_distinct_conv_prefix set_append)
using assms
apply (metis Un_iff append_Cons distinct_append distinct_map eq_key_imp_eq_value in_set_conv_decomp
    not_distinct_conv_prefix set_append)
done


lemma lsubst_lemma2:
  assumes "z \<in> set (map fst xs)"
  shows "\<exists>v ys1 ys3. (xs = ys1 @ [(z, v)] @ ys3)"
using assms
proof (induct xs arbitrary: z)
  case Nil
  then show ?case
  apply auto
  done
next
  case (Cons a ys1)
  then show ?case
  apply auto
  apply (metis append_Nil eq_fst_iff)
  by (meson in_set_conv_decomp_first list.set_intros(2))
qed


lemma lsubst_lemma3:
  assumes "distinct (map fst xs)"
  assumes "z \<in> set (map fst xs)"
  shows "\<exists>v ys1 ys3. (xs = ys1 @ [(z, v)] @ ys3
    \<and> z \<notin> set (map fst ys1)
    \<and> z \<notin> set (map fst ys3))"
  by (metis assms(1,2) lsubst_lemma1(1,2) lsubst_lemma2)


lemma lsubst_lemma4:
  assumes "distinct (map fst xs)"
  assumes "(k, v) \<in> set xs"
  shows "\<exists>ys1 ys3. (xs = ys1 @ [(k, v)] @ ys3
    \<and> k \<notin> set (map fst ys1)
    \<and> k \<notin> set (map fst ys3))"
by (metis append.left_neutral append_Cons assms(1,2) in_set_conv_decomp_last lsubst_lemma1(1,2))


lemma lsubst_lemma5:
  assumes "distinct (map fst xs)"
  assumes "(k, v) \<in> set xs"
  shows "lsubst xs k = v"
by (metis assms(1,2) lsubst.simps(2) lsubst_ignore_beforeafters lsubst_lemma4)


lemma lsubst_lemma6:
  assumes "distinct (map fst xs)"
  assumes "distinct (map fst ys)"
  assumes "k \<in> set (map fst xs)"
  assumes "set xs = set ys"
  shows "lsubst xs k = lsubst ys k"
using assms(1,2,3,4) lsubst_lemma5 by auto


(* リンク代入に余計なものを加えても結果は同じ． *)
lemma lsubst_lemma7:
  assumes "distinct (map fst xs)"
  assumes "distinct (map fst ys)"
  assumes "k \<in> set (map fst xs)"
  assumes "set xs \<subseteq> set ys"
  shows "lsubst xs k = lsubst ys k"
using Un_iff assms(1,2,3,4) lsubst_lemma2 lsubst_lemma5 set_append by auto


(* リンク代入の順番を入れ替えたとしても同じになる． *)
lemma lsubst_distinct:
  assumes "distinct (map fst xs)"
  assumes "distinct (map fst ys)"
  assumes "set xs = set ys"
  shows "lsubst xs k = lsubst ys k"
by (metis assms(1,2,3) lsubst_ignore lsubst_lemma6)


(* リンク代入の順番を入れ替えたとしても同じになる． *)
lemma lmap_lsubst_distinct:
  assumes "distinct (map fst xs)"
  assumes "distinct (map fst ys)"
  assumes "set xs = set ys"
  shows "lmap (lsubst xs) g = lmap (lsubst ys) g"
by (metis (no_types, lifting) ext assms(1,2,3) lsubst_distinct)


lemma lsubst_filter:
  assumes "z \<in> S"
  assumes "ys = filter (\<lambda>x. fst x \<in> S) xs"
  shows "lsubst xs z = lsubst ys z"
using assms
proof (induct xs arbitrary: ys S)
  case Nil
  then show ?case 
  apply auto
  done
next
  case (Cons a xs)
  then show ?case 
  apply (simp_all add: lsubst_simp)
  by auto
qed


lemma map_lsubst_filter:
  assumes "set zs \<subseteq> S"
  assumes "ys = filter (\<lambda>x. fst x \<in> S) xs"
  shows "map (lsubst xs) zs = map (lsubst ys) zs"
using assms
proof (induct xs arbitrary: ys S)
  case Nil
  then show ?case 
  apply auto
  done
next
  case (Cons a xs)
  then show ?case 
  apply (simp_all add: lsubst_simp)
  by auto
qed


lemma fmap_lsubst_filter:
  assumes "fset zs \<subseteq> S"
  assumes "ys = filter (\<lambda>x. fst x \<in> S) xs"
  shows "(lsubst xs) |`| zs = (lsubst ys) |`| zs"
proof -
  have "\<forall>z |\<in>| zs. z \<in> S"
    using assms(1) by blast

  then have "\<forall>z |\<in>| zs. (lsubst xs z = lsubst ys z)"
    using assms(2) lsubst_filter by blast

  then show ?thesis 
    by auto
qed


subsection\<open>Basic Property of Link Substitution Over Types\<close>


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
    apply (simp add: FLrhs_def)
    using FLfusion_set_def by auto
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



lemma lsubst_graph_freelinks_subset:
  assumes "length xs = length ys"
  assumes "FL G \<subseteq> set xs"
  assumes "distinct xs"
  shows "FL (lmap (lsubst (zip xs ys)) G) \<subseteq> set ys"
proof -
  have P1: "FL (lmap (lsubst (zip xs ys)) G) \<subseteq> (lsubst (zip xs ys)) ` FL G"
    by (simp add: FL_lmap_commute)
  have P2: "lsubst (zip xs ys) ` set xs = set ys"
    by (metis assms(1,3) lsubst_image map_fst_zip map_snd_zip)
  then have P3: "lsubst (zip xs ys) ` FL G \<subseteq> set ys"
    using assms(2) by blast
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
apply (induct g arbitrary: f rule: graph.induct[of _ "%_. True" "%_. True"])
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


lemma lift_graph_make_diffgraph_equiv:
  "lift_graph i (make_diffgraph rhs) = make_diffgraph rhs"
proof -
  obtain j C zs fusions taus where
    rhs: "rhs = (j, (C, zs), fusions, taus)"
    by (metis surj_pair)

  have P2: "make_diffgraph rhs = Mols1 (Atom (GConstr C) zs) (fusions_of fusions)"
    apply (simp add: make_diffgraph_def)
    using rhs by auto

  then show ?thesis
    by (simp add: lift_graph_Mols1_equiv lift_graph_fusions_of)
qed


lemma lift_graph_lbind_com:
  "lift_graph i (lbind x g) = lbind x (lift_graph i g)"
by (simp add: lbind_def lift_graph_lmap_commute)


lemma lift_graph_lbind_links_equiv:
  "lift_graph i (fold lbind ys T) = fold lbind ys (lift_graph i T)"
apply (induction ys arbitrary: T)
apply simp
by (simp add: lift_graph_lbind_com)


lemma lift_graph_lbinds_equiv:
   "lift_graph i (lbinds ys T) = lbinds ys (lift_graph i T)"
by (simp add: lbinds_def lift_graph_lbind_links_equiv)


lemma FL_lbinds:
   "FL (lbinds ys g) = FL g - set ys"
proof (induct ys arbitrary: g)
  case Nil
  then show ?case
  apply auto
  apply (simp_all add: lbinds_def)
  done
next
  case (Cons a ys)
  then show ?case
  apply auto
  apply (simp_all add: lbinds_def)
  apply (simp_all add: lbind_hide)
  done
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
  "(\<forall>x \<in> FL G. f x = g x) ==> lmap f G = lmap g G"
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


(* リンク代入を自由リンクでない domain で拡張しても結果は変わらないという証明． *)


lemma lmap_lim2:
  assumes "ys = xs1 @ xs2"
  assumes "set (map fst xs1) \<inter> FLG = {}"
  shows "\<forall>x \<in> FLG. lsubst xs2 x = lsubst ys x"
using lsubst_ignore_befores assms apply auto
by (metis IntI emptyE)


lemma lmap_lim_helper:
  assumes "set ys = set xs1 \<union> set xs2"
  shows "set ys = set (xs1 @ xs2)"
by (simp add: assms)


lemma lmap_lim3:
  assumes "set ys = set xs1 \<union> set xs2"
  assumes "distinct (map fst ys)"
  assumes "distinct (map fst xs2)"
  assumes "set (map fst xs1) \<inter> FLG = {}"
  shows "\<forall>x \<in> FLG. lsubst xs2 x = lsubst ys x"
by (smt (verit, best) Un_commute Un_iff assms(1,2,3,4) disjoint_iff image_Un list.set_map lsubst_ignore
    lsubst_lemma7 sup_ge1)


lemma lmap_lim4:
  assumes "set ys = set xs1 \<union> set xs2"
  assumes "distinct (map fst ys)"
  assumes "distinct (map fst xs2)"
  assumes "set (map fst xs1) \<inter> FL G = {}"
  shows "lmap (lsubst xs2) G = lmap (lsubst ys) G"
by (meson assms(1,2,3,4) lmap_lim lmap_lim3)



lemma lmap_lim5:
  assumes "xs = filter (\<lambda>x. fst x \<in> FLG) ys"
  shows "\<exists>xs1. (set ys = set xs1 \<union> set xs \<and> set (map fst xs1) \<inter> FLG = {})"
using assms
proof (induct ys arbitrary: xs)
  case Nil
  then show ?case
  apply auto
  done
next
  case (Cons a ys)
  then show ?case
  apply auto
  by (metis (no_types, lifting) Un_insert_left image_insert insert_disjoint(2) list.simps(15))
qed


lemma lmap_restriction:
  assumes "distinct (map fst ys)"
  assumes "xs = filter (\<lambda>x. fst x \<in> FL G) ys"
  shows "lmap (lsubst xs) G = lmap (lsubst ys) G"
using assms
proof -
  have P1: "distinct (map fst xs)"
    using assms(1,2) distinct_map_filter by blast
  have P2: "\<exists>xs1. (set ys = set xs1 \<union> set xs
    \<and> set (map fst xs1) \<inter> FL G = {})"
   using assms(2) lmap_lim5 by blast
  then show ?thesis
  using P1 assms(1) lmap_lim4 by blast
qed


lemma lmap_ty_lim4:
  assumes "set ys = set xs1 \<union> set xs2"
  assumes "distinct (map fst ys)"
  assumes "distinct (map fst xs2)"
  assumes "set (map fst xs1) \<inter> ALty ty = {}"
  shows "lmap_ty (lsubst xs2) ty = lmap_ty (lsubst ys) ty"
using assms
proof (induct ty)
  case (TBase x1 x2)
  then show ?case 
  apply auto
  by (simp add: lmap_lim3)
next
  case (TArrow ty1 ty2 x3)
  then show ?case 
  apply auto
  by (simp add: lmap_lim3)
next
  case (TLI x1 x2 x3 x4)
  then show ?case 
  apply auto
  apply (simp_all add: lmap_lim3)
  by (smt (verit, ccfv_SIG) UN_absorb Un_empty inf_sup_distrib1 multiset.map_cong)
qed


lemma lmap_ty_lim5:
  assumes "set xs \<subseteq> set ys"
  assumes "distinct (map fst ys)"
  assumes "distinct (map fst xs)"
  assumes "set (map fst xs) = ALty ty"
  shows "lmap_ty (lsubst xs) ty = lmap_ty (lsubst ys) ty"
proof -
  obtain xs1 where
    xs1: "xs1 = filter (\<lambda>x. fst x \<notin> ALty ty) ys"
    by presburger
  then have P1: "set ys = 
    set (filter (\<lambda>x. fst x \<notin> ALty ty) ys) \<union> 
    set (filter (\<lambda>x. fst x \<in> ALty ty) ys)"
    by auto

  have P2: "set (filter (\<lambda>x. fst x \<in> ALty ty) ys) = set xs"
    apply auto
    apply (metis (no_types, lifting) append_Cons assms(1,2,3,4) eq_key_imp_eq_value in_mono
      in_set_conv_decomp lsubst_lemma3) (* 3.0s *)
    using assms(1) apply blast
    by (metis assms(4) in_set_zipE zip_map_fst_snd)

  then have P1: "set ys = set xs1 \<union> set xs"
    using P1 xs1 by argo

  have P2: "set (map fst xs1) \<inter> ALty ty = {}"
    apply auto
    by (simp add: xs1)
  
  show ?thesis
    using P1 P2 assms(2,3) lmap_ty_lim4 by blast
qed


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



(* 型のリンク代入に関する補題を移動． *)

(* 型のリンク代入を二回やると元に戻るという定理．
これは ALty においてのみ成り立つことに注意する． *)
lemma lmap_ty_inv_inv:
  assumes "distinct (map fst xs)"
  assumes "distinct (map snd xs)"
  assumes "ALty ty \<subseteq> set (map fst xs)"
  shows  "lmap_ty (lsubst (swap_list xs)) (lmap_ty (lsubst xs) ty) = ty"
using assms
proof (induct ty arbitrary: xs)
  case (TBase x1 x2)
  then show ?case
  apply auto
  by (metis ALty.simps(1) TBase.prems(3) map_lsubst_inv_inv swap_map_snd swap_swap_list)
next
  case (TArrow ty1 ty2 x3)
  then show ?case
  apply auto
  by (metis ALty.simps(2) TArrow.prems(3) map_lsubst_inv_inv swap_map_fst swap_swap_list)
next
  case (TLI taus alpha zs ys)

  have "\<forall>ty \<in># taus. ALty ty \<subseteq> set (map fst xs)"
    using TLI.prems(3) by auto

  then have "\<forall>ty \<in># taus. (lmap_ty (lsubst (swap_list xs))) (lmap_ty (lsubst xs) ty) = ty"
    using TLI.hyps TLI.prems(1,2) by blast

  then have "image_mset ((lmap_ty (lsubst (swap_list xs))) \<circ> (lmap_ty (lsubst xs))) taus = taus"
    by (simp add: multiset.map_ident_strong)

  then have P1: "image_mset (lmap_ty (lsubst (swap_list xs))) (image_mset (lmap_ty (lsubst xs)) taus) = taus"
    by (simp add: image_mset.compositionality)

  have P2: "set zs \<subseteq> set (map fst xs)"
    using TLI.prems(3) by auto

  have P3: "fset ys \<subseteq> set (map fst xs)"
    using TLI.prems(3) by auto

  show ?case
  apply auto
   using P1 apply order
  apply (metis P2 TLI.prems(2) map_lsubst_inv_inv swap_map_snd swap_swap_list)
  using P3 TLI.prems(2) lsubst_inv_inv2 apply fastforce
  by (metis (no_types, lifting) P3 TLI.prems(2) imageI lsubst_inv_inv2 subset_eq)
qed



(* 型付けの両辺で自由リンクの集合が等しいという定理をここから証明していく． *)

(* この補題は TyAlpha の inversion を示す上でも重要． *)
lemma FL_ty_lmap:
  assumes A1: "FLty ty = set xs"
  assumes A2: "length xs = length ys"
  assumes A3: "distinct xs"
  shows "FLty (lsubst_ty xs ys ty) = set ys"
apply (cases ty)
apply (simp_all add: FLty_def)
using A1 A2 A3 FLty.simps(1) lsubst_ty_def lsubst_zip_image by auto



lemma FL_ty_lmap2:
  assumes A1: "FLty ty = set (map fst xs)"
  assumes A3: "distinct (map fst xs)"
  shows "FLty (lmap_ty (lsubst xs) ty) = set (map snd xs)"
by (metis A1 A3 FL_ty_lmap length_map lsubst_ty_def zip_map_fst_snd)




lemma FL_ty_lmap3:
  assumes "FLty ty = set (map fst xs2)"
  assumes "set ys = set xs1 \<union> set xs2"
  assumes "distinct (map fst ys)"
  assumes "distinct (map fst xs2)"
  shows "FLty (lmap_ty (lsubst xs2) ty) = FLty (lmap_ty (lsubst ys) ty)"
using assms
proof (cases ty)
  case (TBase x11 x12)
  then show ?thesis
  apply auto
  using assms(1,2,3,4) lsubst_lemma7 apply auto[1]
  using assms(1,2,3,4) lsubst_lemma7 apply auto[1]
  done
next
  case (TArrow x21 x22 x23)
  then show ?thesis
  apply auto
  using assms(1,2,3,4) lsubst_lemma7 apply auto[1]
  using assms(1,2,3,4) lsubst_lemma7 apply auto[1]
  done
next
  case (TLI x31 x32 x33 x34)
  then show ?thesis
  apply auto
  using assms(1,2,3,4) lsubst_lemma7 apply auto[1]
  using assms(1,2,3,4) lsubst_lemma7 apply auto[1]
  done
qed



lemma FL_typing_rel_eq_lemma1:
  assumes "distinct (map fst xs)"
  assumes "distinct (map fst xs2)"
  assumes "FL G = set (map fst xs2)"
  assumes "set xs2 \<subseteq> set xs"
  shows "FL (lmap (lsubst xs) G) = FL (lmap (lsubst xs2) G)"
by (metis assms(1,2,3,4) lmap_lim lsubst_lemma7)


lemma FL_typing_rel_eq_lemma2:
  assumes "distinct (map fst xs)"
  assumes "distinct (map fst xs2)"
  assumes "FLty ty = set (map fst xs2)"
  assumes "set xs2 \<subseteq> set xs"
  shows "FLty (lmap_ty (lsubst xs) ty) = FLty (lmap_ty (lsubst xs2) ty)"
using FL_ty_lmap3 assms(1,2,3,4) by blast


lemma FL_typing_rel_eq_lemma3:
  assumes "distinct (map fst xs)"
  assumes "distinct (map fst xs2)"
  assumes "FL G = FLty ty"
  assumes "FL G = set (map fst xs2)"
  assumes "set xs2 \<subseteq> set xs"
  shows "FL (lmap (lsubst xs) G) = FLty (lmap_ty (lsubst xs) ty)"
by (metis FL_lmap_commute FL_ty_lmap2 FL_typing_rel_eq_lemma1
    FL_typing_rel_eq_lemma2 assms(1,2,3,4,5) lsubst_image)



lemma FL_typing_rel_eq_lemma4:
  assumes "distinct (map fst xs)"
  assumes "FLG \<subseteq> set (map fst xs)"
  assumes "xs2 = filter (\<lambda>x. fst x \<in> FLG) xs"
  shows "(distinct (map fst xs2)
    \<and> set xs2 \<subseteq> set xs
    \<and> FLG = set (map fst xs2))"
apply auto
using assms(1,3) distinct_map_filter apply blast
apply (simp add: assms(3))
using assms(2,3) apply auto[1]
by (simp add: assms(3))


lemma FL_typing_rel_eq_lemma5:
  assumes "distinct (map fst xs)"
  assumes "FLG \<subseteq> set (map fst xs)"
  shows "\<exists>xs2. (distinct (map fst xs2)
  \<and> set xs2 \<subseteq> set xs
  \<and> FLG = set (map fst xs2))"
by (meson FL_typing_rel_eq_lemma4 assms(1,2))


lemma FL_typing_rel_eq_lemma6:
  assumes "distinct (map fst xs)"
  assumes "FL G = FLty ty"
  assumes "FL G \<subseteq> set (map fst xs)"
  shows "FL (lmap (lsubst xs) G) = FLty (lmap_ty (lsubst xs) ty)"
by (meson FL_typing_rel_eq_lemma3 FL_typing_rel_eq_lemma5
    assms(1,2,3))


lemma FL_typing_rel_eq_lemma7:
  assumes "set xs = ALty ty"
  assumes "length xs = length ys"
  assumes "distinct xs"
  assumes "distinct ys"
  assumes "FL G \<subseteq> set xs"
  assumes "FL G = FLty ty"
  shows "FL (lmap (lsubst (zip xs ys)) G) = FLty (lsubst_ty xs ys ty)"
by (metis FL_typing_rel_eq_lemma6 assms(2,3,5,6) lsubst_ty_def
    map_fst_zip)


lemma FL_typing_rel_eq_lemma8:
  assumes "FL T = set ys"
  assumes "set xs \<subseteq> FL T"
  shows "FL (lbinds (filter (\<lambda>y. y \<notin> set xs) ys) T) = set xs"
by (metis Diff_Diff_Int FL_lbinds Int_commute Un_Int_eq(4) assms(1,2)
    set_diff_eq set_filter sup.order_iff)


lemma lsubst_ideal_aux:
  assumes "s = s1 @ s2"
  assumes "distinct (map fst s)"
  assumes "map fst s1 = map snd s1"
  shows "lsubst s z = lsubst s2 z"
using assms
proof (induct s1 arbitrary: s2 z s)
  case Nil
  then show ?case
  apply auto
  done
next
  case (Cons a s3)
  then show ?case
  apply auto
  by (metis list.set_map lsubst_ignore lsubst_simp map_eq_conv)
qed


lemma lsubst_ideal:
  assumes "set s = set s1 \<union> set s2"
  assumes "distinct (map fst s)"
  assumes "distinct (map fst s2)"
  assumes "map fst s1 = map snd s1"
  shows "lsubst s z = lsubst s2 z"
by (smt (verit) UnE Un_upper2 assms(1,2,3,4) image_iff list.set_map
    lsubst_ignore lsubst_lemma5 lsubst_lemma7 map_eq_conv
    surjective_pairing)


lemma lmap_union_ideal:
  assumes "set s = set s1 \<union> set s2"
  assumes "distinct (map fst s)"
  assumes "distinct (map fst s2)"
  assumes "map fst s1 = map snd s1"
  shows "lmap (lsubst s) g = lmap (lsubst s2) g"
using assms(1,2,3,4) lsubst_ideal by presburger


lemma lmap_ty_union_ideal:
  assumes "set s = set s1 \<union> set s2"
  assumes "distinct (map fst s)"
  assumes "distinct (map fst s2)"
  assumes "map fst s1 = map snd s1"
  shows "lmap_ty (lsubst s) ty = lmap_ty (lsubst s2) ty"
using assms(1,2,3,4) lsubst_ideal by presburger


(* グラフの型付けの両辺で自由リンク集合が等しい．
あくまでグラフであり，一般の指揮に対する性質ではないことに注意．
*)
lemma FL_typing_LRHS:
  assumes "\<Gamma> \<turnstile>{P} G : ty"
  assumes "G = Graph g"
  shows "FL g = FLty ty"
using assms
proof (induction arbitrary: g set: typing)
  case (TyVar i \<Gamma> xs ty ys P)
  then show ?case
  using FL_ty_lmap2 by force
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
  case (TyAlpha \<Gamma>2 P G ty xs ys)
  then show ?case
  by (metis FL_typing_rel_eq_lemma7 exp.inject(1))
next
  case (TyCase \<Gamma> P e0 ty1 \<Gamma>2 e1 ty2 e2 T)
  then show ?case
  by auto
next
  case (TyLIIntro lhs rhs P \<Gamma>)
  then show ?case
  apply auto
  apply (metis TyLIIntro_freelinks_equiv surj_pair)
  apply (metis TyLIIntro_freelinks_equiv surj_pair)
  done
next
  case (TyLITrans \<Gamma> P T1 a2 xs2 tys1 a1 xs1 ys1 T2 tys2 ys2 ys)
  then show ?case
  by force
next
  case (TyLIIntro0 \<Gamma> P T a xs)
  then show ?case
  by (simp add: fset_of_list.rep_eq)
next
  case (TyLIElim0 ys ys' xs T \<Gamma> P a)
  then show ?case
  by (metis FL_typing_rel_eq_lemma8 FLty.simps(1,3) exp.inject(1) fset_of_list.rep_eq)
qed


(* TyVar における FLty を domain に持つリンク代入を
domain が ALty になるように拡張するための定理群． *)
lemma LLty_union_ideal_aux:
  assumes "finite S"
  shows "\<exists>ys.(set (map fst ys) = S
  \<and> distinct (map fst ys)
  \<and> distinct (map snd ys)
  \<and> map fst ys = map snd ys)"
proof -
  obtain xs where xs:
    "set xs = S" "distinct xs"
    using assms by (meson finite_distinct_list)

  let ?ys = "map (\<lambda>x. (x, x)) xs"

  have P1: "set (map fst ?ys) = S" using xs by auto
  moreover have "distinct (map fst ?ys)"
    by (simp add: map_idI xs(2))
  moreover have P2: "map fst ?ys = map snd ?ys"
    by auto
  ultimately show ?thesis
    apply auto
    by (metis (no_types, lifting) P1 P2 list.map_comp list.set_map
      map_eq_conv)
qed



lemma LLty_union_ideal:
  assumes A1: "distinct (map fst xs)"
  assumes A2: "distinct (map snd xs)"
  assumes A3: "set (map fst xs) = FLty ty"
  assumes A5: "set (map snd xs) \<inter> ALty ty - FLty ty = {}"
  shows "\<exists>ys.(set (map fst ys) = ALty ty
  \<and> distinct (map fst ys)
  \<and> distinct (map snd ys)
  \<and> lmap_ty (lsubst ys) ty = lmap_ty (lsubst xs) ty
  \<and> lmap (lsubst ys) G = lmap (lsubst xs) G)"
proof -
  have "finite (ALty ty - FLty ty)"
    by (simp add: finite_ALty)
  then obtain ys ys1 where
    P3: "set (map fst ys1) = ALty ty - FLty ty
    \<and> distinct (map fst ys1)
    \<and> distinct (map snd ys1)
    \<and> ys = ys1 @ xs
    \<and> map fst ys1 = map snd ys1"
    by (meson LLty_union_ideal_aux)

  have "set (map fst ys1) \<inter> set (map fst xs) = {}"
    by (metis Diff_disjoint P3 A3 inf_commute)
  then have P5: "distinct (map fst ys)"
    by (simp add: P3 A1)

  have "set (map snd ys1) \<inter> set (map snd xs) = {}"
    by (metis Int_Diff P3 A5 inf_commute)
  then have P7: "distinct (map snd ys)"
    by (simp add: P3 A2)

  have P10: "set (map fst ys) = ALty ty"
   proof -
     have "set (map fst ys) =
           set (map fst ys1) \<union> set (map fst xs)"
       by (simp add: P3)
     also have "... = (ALty ty - FLty ty) \<union> FLty ty"
       using A3 P3 by blast
     also have "... = ALty ty"
       using FLty_subset_ALty by blast
     finally show ?thesis .
   qed

  have P8: "lmap_ty (lsubst ys) ty = lmap_ty (lsubst xs) ty"
    using P3 P5 lsubst_ideal_aux by presburger
  have P9: "lmap (lsubst ys) G = lmap (lsubst xs) G"
    using P3 P5 lsubst_ideal_aux by presburger

  show ?thesis
    using P10 P5 P7 P8 P9 by blast
qed



lemma TyAlphaWhenTyVar:
  assumes A0: "\<Gamma> \<turnstile>{P} Graph g : ty"
  assumes A1: "set (map fst xs) = FLty ty"
  assumes A2: "distinct (map fst xs)"
  assumes A3: "distinct (map snd xs)"
  assumes A4: "set (map snd xs) \<inter> ALty ty - FLty ty = {}"
  shows   "\<Gamma> \<turnstile>{P} Graph (lmap (lsubst xs) g) : lmap_ty (lsubst xs) ty"
proof -
  obtain ys where
  ys: "set (map fst ys) = ALty ty
       \<and> distinct (map fst ys)
       \<and> distinct (map snd ys)
       \<and> lmap_ty (lsubst ys) ty = lmap_ty (lsubst xs) ty
       \<and> lmap (lsubst ys) g = lmap (lsubst xs) g"
  using assms LLty_union_ideal by metis

  then have "\<Gamma> \<turnstile>{P} Graph (lmap (lsubst ys) g) : lmap_ty (lsubst ys) ty"
    by (metis A0 FL_typing_LRHS FLty_subset_ALty TyAlpha length_map
      lsubst_ty_def zip_map_fst_snd)
  then have "\<Gamma> \<turnstile>{P} Graph (lmap (lsubst xs) g) : lmap_ty (lsubst xs) ty"
    using ys by argo
  then show ?thesis .
qed


(* 線型含意型の健全性定理のための証明． *)


lemma subst_make_diffgraph_ignore:
  "subst i xs g2 (Graph (make_diffgraph rhs)) = Graph (make_diffgraph rhs)"
apply (simp add: make_diffgraph_def)
by (simp add: split_beta subst_graph_Mols1_equiv
    subst_graph_fusions_of)


lemma subst_mol_distribute:
 "subst i xs g2 (Graph (Mol T1 T2)) =
  Graph (Mol (subst_graph i xs g2 T1) (subst_graph i xs g2 T2))"
by simp


lemma subst_graph_lbind_com:
  assumes "set xs = FL G"
  shows "subst_graph i xs G (lbind x g) = lbind x (subst_graph i xs G g)"
apply (simp add: lbind_def)
by (simp add: assms subst_graph_lmap_commute)


lemma subst_graph_lbinds_com:
  assumes "set xs = FL G"
  shows "subst_graph i xs G (lbinds ys g) = lbinds ys (subst_graph i xs G g)"
using assms
apply (simp add: lbinds_def)
proof (induct ys arbitrary: g i xs G)
  case Nil
  then show ?case
  by simp
next
  case (Cons a ys)
  then show ?case
  apply auto
  by (simp add: subst_graph_lbind_com)
qed



(* ここから inversion lemma を示すための補題． *)


(* この補題は TyAlpha の inversion を示す上で重要． *)
lemma ALty_lmap:
  assumes A1: "ALty ty = set (map fst xs)"
  assumes A2: "set xs \<subseteq> set ys"
  assumes A3: "distinct (map fst ys)"
  assumes A4: "distinct (map fst xs)"
  shows "ALty (lmap_ty (lsubst ys) ty) = set (map snd xs)"
using assms
proof (induct ty arbitrary: xs ys)
  case (TBase x1 x2)
  then show ?case
  apply auto
  apply (metis imageI lsubst_lemma5 snd_conv subset_code(1))
  by (metis fst_conv image_eqI lsubst_lemma5 subset_iff)
next
  case (TArrow ty1 ty2 x3)
  then show ?case
  apply auto
  apply (metis image_eqI lsubst_lemma5 snd_eqD subsetD)
  by (metis fst_conv imageI lsubst_lemma5 subset_eq)
next
  case (TLI tys a vs zs)
  have P1:
    "\<Union> (set_mset (image_mset ALty tys)) \<union> set vs \<union> fset zs
     = set (map fst xs)"
    using ALty.simps(3) TLI.prems(1) by presburger

  have P45:
    "ALty (lmap_ty (lsubst xs) (TLI tys a vs zs)) =
     ALty (lmap_ty (lsubst ys) (TLI tys a vs zs))"
    using TLI.prems(1,2,3,4) lmap_ty_lim5 by presburger


  obtain xs_tys where
    xs_tys: "xs_tys = filter (\<lambda>x. fst x \<in> \<Union> (set_mset (image_mset ALty tys))) xs"
    by presburger

  have xs_tys_P1: "set xs_tys \<subseteq> set xs"
    using xs_tys by auto
  have xs_tys_P2: "distinct (map fst xs_tys)"
    using TLI.prems(4) distinct_map_filter xs_tys by blast
  have xs_tys_P3:
    "\<Union> (set_mset (image_mset ALty tys)) = set (map fst xs_tys)"
    using xs_tys apply auto
    using P1 by fastforce

  obtain sigma_of_tau where
    sigma_of_tau: "sigma_of_tau = (\<lambda>ty. filter (\<lambda>x. fst x \<in> ALty ty) xs_tys)"
    by presburger

  have
    "\<forall>ty \<in># tys. ALty ty \<subseteq> set (map fst xs_tys)"
    using xs_tys_P3 by auto
  then have sigma_of_tau_P1:
    "\<forall>ty \<in># tys. (ALty ty = set (map fst (sigma_of_tau ty)))"
    apply (simp_all add: sigma_of_tau)
    by auto

  then have P9:
    "(\<Union>ty \<in> set_mset tys. set (sigma_of_tau ty)) = set xs_tys"
    apply auto
    apply (simp_all add: sigma_of_tau)
    by (simp add: xs_tys)
  then have P20:
    "(\<Union>ty \<in> set_mset tys. (set (map snd (sigma_of_tau ty)))) =
     set (map snd xs_tys)"
    by (metis (no_types, lifting) ext image_UN image_set)


  have sigma_of_tau_P2:
    "\<forall>ty \<in># tys. \<forall>xs_ty.
    (xs_ty = sigma_of_tau ty --> (set xs_ty \<subseteq> set xs_tys
    \<and> distinct (map fst xs_ty)
    \<and> ALty ty = set (map fst xs_ty)))"
    apply auto
    apply (simp add: sigma_of_tau)
    apply (simp add: distinct_map_filter sigma_of_tau xs_tys)
    using TLI.prems(4) distinct_map_filter apply blast
    apply (simp add: sigma_of_tau_P1)
    by (simp add: sigma_of_tau)

  have P4:
    "\<forall>ty \<in># tys.
     ALty (lmap_ty (lsubst (sigma_of_tau ty)) ty) = set (map snd (sigma_of_tau ty))"
    by (simp add: TLI.hyps sigma_of_tau_P2)
  then have P6:
    "\<forall>ty \<in># tys.
     ALty (lmap_ty (lsubst xs) ty) = set (map snd (sigma_of_tau ty))"
    by (meson TLI.hyps TLI.prems(4) order_trans sigma_of_tau_P2
      xs_tys_P1)
  then have P7:
    "\<forall>ty \<in># tys.
     ALty (lmap_ty (lsubst ys) ty) = set (map snd (sigma_of_tau ty))"
    by (meson TLI.hyps TLI.prems(2,3) sigma_of_tau_P2 subset_trans
      xs_tys_P1)
  then have P8:
    "(\<Union>ty \<in> set_mset tys. (ALty (lmap_ty (lsubst ys) ty))) =
     (\<Union>ty \<in> set_mset tys. (set (map snd (sigma_of_tau ty))))"
    by blast
  then have P12:
    "(\<Union>ty \<in> set_mset tys. (ALty (lmap_ty (lsubst ys) ty))) =
     set (map snd xs_tys)"
    using P20 by order
  then have P14:
    "\<Union> (set_mset (image_mset ALty (image_mset (lmap_ty (lsubst ys)) tys))) =
     set (map snd xs_tys)"
    by auto

  have vs_aux1: "set (map fst ((filter (\<lambda>x. fst x \<in> set vs) xs))) = set vs"
    apply auto
    using P1 list.set_map by auto
  have vs_aux_distinct: "distinct (map fst ((filter (\<lambda>x. fst x \<in> set vs) xs)))"
    by (simp add: TLI.prems(4) distinct_map_filter)
  then have vs_aux1:
    "set (map (lsubst (filter (\<lambda>x. fst x \<in> set vs) xs)) vs) =
     set (map snd (filter (\<lambda>x. fst x \<in> set vs) xs))"
    by (metis (lifting) image_set lsubst_image vs_aux1)
  have vs_cdom2:
    "map (lsubst (filter (\<lambda>x. fst x \<in> set vs) xs)) vs = map (lsubst xs) vs"
    apply auto
    by (metis lsubst_filter)
  then have vs_cdom:
    "set (map (lsubst xs) vs) =
     set (map snd (filter (\<lambda>x. fst x \<in> set vs) xs))"
    using vs_aux1 by presburger
  then have vs_cdom3:
    "(lsubst xs) ` set vs =
     set (map snd (filter (\<lambda>x. fst x \<in> set vs) xs))"
     by auto

  have zs_aux1: "set (map fst ((filter (\<lambda>x. fst x \<in> fset zs) xs))) = fset zs"
    apply auto
    using P1 list.set_map by auto
  have zs_aux_distinct: "distinct (map fst ((filter (\<lambda>x. fst x \<in> fset zs) xs)))"
    by (simp add: TLI.prems(4) distinct_map_filter)
  then have zs_aux1:
    "fset ((lsubst (filter (\<lambda>x. fst x \<in> fset zs) xs)) |`| zs) =
     set (map snd (filter (\<lambda>x. fst x \<in> fset zs) xs))"
    by (metis fimage.rep_eq lsubst_image zs_aux1)
  have zs_cdom2:
    "(lsubst (filter (\<lambda>x. fst x \<in> fset zs) xs)) |`| zs = (lsubst xs) |`| zs"
    by (metis dual_order.refl fmap_lsubst_filter)
  then have zs_cdom:
    "fset ((lsubst xs) |`| zs) =
     set (map snd (filter (\<lambda>x. fst x \<in> fset zs) xs))"
    using zs_aux1 by presburger
  then have zs_cdom3:
    "(lsubst xs) ` fset zs =
     set (map snd (filter (\<lambda>x. fst x \<in> fset zs) xs))"
    by auto

  have P50:
    "set (map snd xs_tys) =
     (\<Union> (set_mset (image_mset ALty (image_mset (lmap_ty (lsubst xs)) tys))))"
    apply auto
    apply (metis (no_types, lifting) P12 P6 P8 UN_E imageI list.set_map snd_eqD)
    using P12 P6 P8 by auto

  have P40:
    "set xs =
     set (filter (\<lambda>x. fst x \<in> \<Union> (set_mset (image_mset ALty tys))) xs) \<union>
     set (filter (\<lambda>x. fst x \<in> set vs) xs) \<union>
     set (filter (\<lambda>x. fst x \<in> fset zs) xs)"
     using P1 by auto
  then have P41:
    "set xs =
     set xs_tys \<union>
     set (filter (\<lambda>x. fst x \<in> set vs) xs) \<union>
     set (filter (\<lambda>x. fst x \<in> fset zs) xs)"
     using xs_tys by presburger
  then have P42:
    "set (map snd xs) =
     set (map snd xs_tys) \<union>
     set (map snd (filter (\<lambda>x. fst x \<in> set vs) xs)) \<union>
     set (map snd (filter (\<lambda>x. fst x \<in> fset zs) xs))"
     by auto
  then have P43:
    "set (map snd xs) =
     (\<Union> (set_mset (image_mset ALty (image_mset (lmap_ty (lsubst xs)) tys)))) \<union>
     lsubst xs ` fset zs \<union>
     lsubst xs ` set vs"
    using P50 vs_cdom3 zs_cdom3 by force
  then have P44:
    "set (map snd xs) = ALty (lmap_ty (lsubst xs) (TLI tys a vs zs))"
    using ALty.simps(3) P42 P50 lmap_ty.simps(3) vs_cdom zs_cdom by presburger
  then show ?case
    using P45 by presburger
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
  case (TyVar j \<Gamma> xs s ys ty P)
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
  using True le_i len_ins by linarith

    from le_i True have "(insert_at \<Gamma> i (ys, ty2)) ! j = \<Gamma> ! j"
      by (simp add: shift_gt)

    with lookup have "(insert_at \<Gamma> i (ys, ty2)) ! j = (xs, ty)"
      using TyVar.hyps(4) by force

    with j_lt' len_vs
    show ?thesis
      by (metis P1 TyVar.hyps(5,6,7,8) lift.simps(1) lift_graph.simps(2) lookup typing.TyVar)
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
      using TyVar.hyps(4) by presburger

    with Sucj_lt_ins len_vs
    show ?thesis
      by (metis P1 TyVar.hyps(5,6,7,8) lift.simps(1) lift_graph.simps(2) lookup typing.TyVar)
  qed

next
  case (TyLIIntro lhs rhs P \<Gamma>)
  then show ?case
    by (simp add: lift_graph_make_diffgraph_equiv typing.TyLIIntro)

next
  case (TyLITrans \<Gamma> P T1 a2 xs2 tys1 a1 xs1 ys1 T2 tys2 ys2)
  then show ?case
  by (metis lift.simps(1) lift_graph.simps(4) typing.TyLITrans)
next
  case (TyLIElim0 zs ys' xs T \<Gamma> P a)
  have "insert_at \<Gamma> i (ys, ty2) \<turnstile>{P} lift i (Graph T) : TLI {#} a xs zs"
    using TyLIElim0.IH TyLIElim0.prems by blast
  then have "insert_at \<Gamma> i (ys, ty2) \<turnstile>{P} Graph (lift_graph i T) : TLI {#} a xs zs"
    by auto
  then have "insert_at \<Gamma> i (ys, ty2) \<turnstile>{P}
    Graph (lbinds (filter (\<lambda>y. y \<notin> set xs) ys') (lift_graph i T)) : TBase a xs"
    by (simp add: TyLIElim0.hyps(1,2) lift_graph_freelinks typing.TyLIElim0)
  then have "insert_at \<Gamma> i (ys, ty2) \<turnstile>{P}
    Graph (lift_graph i (lbinds (filter (\<lambda>y. y \<notin> set xs) ys') T)) : TBase a xs"
    by (simp add: lift_graph_lbinds_equiv)
  then have "insert_at \<Gamma> i (ys, ty2) \<turnstile>{P}
    lift i (Graph (lbinds (filter (\<lambda>y. y \<notin> set xs) ys') T)) : TBase a xs"
    by simp
  then show ?case
    by blast
next
  case (TyLIIntro0 \<Gamma> P T a xs)
  then show ?case
  by (simp add: typing.TyLIIntro0)
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
    by (metis TyAlpha.hyps(4,5,6) len_xs_vs lift.simps(1) lift_graph_freelinks
      lift_graph_lmap_commute typing.TyAlpha xs_FL)
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


(*
TODO
*)
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
  case (TyVar j \<Gamma> xs' s ys ty' P)
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

    have P2B: "set ys \<inter> ALty ty' - FLty ty' = {}"
      by (simp add: TyVar.hyps(8))

    from TyVar.hyps(4) lookup_shift
    have P2: "\<Gamma>2 ! (j - 1) = (xs', ty')"
      by simp

    moreover have "length xs' = length ys"
      by (simp add: TyVar.hyps(2,3))

    ultimately have
      "\<Gamma>2 \<turnstile>{P} Graph (Atom (GVar (j - 1)) ys) : lmap_ty (lsubst (zip xs' ys)) ty'"
      by (metis P2B TyVar.hyps(2,3,5,6,7) j1_lt_len_\<Gamma>2 lsubst_ty_def typing.TyVar
        zip_map_fst_snd)

    thus ?thesis
      using TyVar.hyps(2,3,5,6,7) P2 j1_lt_len_\<Gamma>2 subst_ij typing.TyVar P2B
    by presburger
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
        using TyVar.hyps(4) TyVar.prems(2) shift_eq by fastforce
    qed
    then have xs'_xs: "xs' = xs" and ty'_ty2: "ty' = ty2"
      by auto

    have len_xs_ys: "length xs = length ys"
      using TyVar.hyps(2,3) xs'_xs by force

    have P2B: "set ys \<inter> ALty ty' - FLty ty' = {}"
      by (simp add: TyVar.hyps(8))

    have subst_eq':
      "subst i xs g2 (Graph (Atom (GVar j) ys))
       = Graph (lmap (lsubst (zip xs ys)) g2)"
      using subst_eq len_xs_ys by simp

    have P3: "s = zip xs ys"
      by (metis TyVar.hyps(2,3) xs'_xs zip_map_fst_snd)

    have "\<Gamma>2 \<turnstile>{P} Graph (lmap (lsubst s) g2) : lmap_ty (lsubst s) ty2"
      using P2B TyAlphaWhenTyVar TyVar.hyps(2,3,5,6,7) TyVar.prems(1) ty'_ty2
      by auto

    then show ?thesis
      using subst_eq' ty'_ty2 xs'_xs P2B P3
      by argo
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
    have lookup2: "\<Gamma>2 ! j = (xs', ty')"
      using TyVar.hyps(4) by argo

    have P2B: "set ys \<inter> ALty ty' - FLty ty' = {}"
      by (simp add: TyVar.hyps(8))


    have j_gt_len_\<Gamma>2: "j < length \<Gamma>2"
    proof -
      from TyVar.hyps(1) len_\<Gamma>1 have "j < length \<Gamma>2 + 1" by simp
      with gt show ?thesis
      using TyVar.prems(2) dual_order.strict_trans1 by blast
    qed

    have "length xs' = length ys"
      using TyVar.hyps(3)
      by (simp add: TyVar.hyps(2))

    then have "\<Gamma>2 \<turnstile>{P} Graph (Atom (GVar j) ys) : lsubst_ty xs' ys ty'"
      by (simp add: P2B TyVar.hyps(5,6,7) j_gt_len_\<Gamma>2 lookup2 lsubst_ty_def
        typing.TyVar)

    thus ?thesis
      using P2B TyVar.hyps(2,3,5,6,7) j_gt_len_\<Gamma>2 lookup2 subst_gt typing.TyVar
      by auto
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
next
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
  case (TyLIIntro lhs rhs P \<Gamma>)
  then show ?case
  using subst_make_diffgraph_ignore typing.TyLIIntro by presburger
next
  case (TyLITrans \<Gamma> P T1 a2 xs2 tys1 a1 xs1 ys1 T2 tys2 ys2 ys)
  then show ?case
  by (smt (z3) subst.simps(1) subst_graph.simps(4) typing.TyLITrans)
next
  case (TyLIElim0 ys ys' vs T \<Gamma> P a)
  then show ?case
  by (simp add: subst_graph_freelinks_equiv subst_graph_lbinds_com
    typing.TyLIElim0)
next
  case (TyLIIntro0 \<Gamma> P T a vs)
  then show ?case
  by (simp add: typing.TyLIIntro0)
qed


subsection \<open>Inversion Lemma\<close>


lemma typing_inv_graph_abs_aux:
  assumes T: "\<Gamma> \<turnstile>{P} e' : ty"
  assumes ty: "ty = TArrow ty1 ty2 zs"
      and E: "e' = Graph g'"
      and C: "g' \<simeq> Atom (GAbs xs ty3 e) ys"
  shows "(xs, ty1) # \<Gamma> \<turnstile>{P} e : ty2"
using assms
proof (induction arbitrary: xs ty1 ty2 zs e ys g' rule: typing.induct)
  case (TyAlpha \<Gamma>2' P g ty' xs' ys')
  (* link α-conversion does not change the fact “g is an abstraction atom up to gcong” *)
  have P1: "FL g \<subseteq> set xs'"
    by (simp add: TyAlpha.hyps(6))
  have P2: "FL (lmap (lsubst (zip xs' ys')) g) \<subseteq> set ys'"
    by (simp add: P1 TyAlpha.hyps(3,4) lsubst_graph_freelinks_subset)
  have P3: "lmap (lsubst (zip xs' ys')) g \<simeq> Atom (GAbs xs ty3 e) ys"
    using TyAlpha.prems(2,3) by blast
  then have P4: "FL (lmap (lsubst (zip xs' ys')) g) = FL (Atom (GAbs xs ty3 e) ys)"
    by (simp add: freelinks_equiv)
  then have P7: "set ys \<subseteq> set ys'"
    using P2 by auto

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
  then have P15: "FLty ty' \<subseteq> set xs'"
    by (simp add: P1)

  have P15B: "set xs' = ALty ty'"
    by (simp add: TyAlpha.hyps(2))

  have P14: "FLty ty' = FL g"
    using FL_typing_LRHS TyAlpha.hyps(1) by presburger
  then have P15: "FLty ty' = set xs'"
    by (metis (no_types, lifting) ALty.simps(2) ALty_lmap FL_lmap_commute
      FL_typing_rel_eq_lemma7 FLty.simps(2) P1 P15B P7 TyAlpha.hyps(3,4,5)
      TyAlpha.prems(1) dual_order.refl lsubst_image lsubst_ty_def map_fst_zip
      map_snd_zip)

  have P10: "lsubst_ty xs' ys' ty' = TArrow ty1 ty2 zs"
     by (simp add: TyAlpha.prems(1))
  have P12: "lsubst_ty ys' xs' (lsubst_ty xs' ys' ty') = lsubst_ty ys' xs' (TArrow ty1 ty2 zs)"
     using P10 by presburger
  have P13: "ty' = lsubst_ty ys' xs' (TArrow ty1 ty2 zs)"
    by (metis P1 P10 P14 P15 P15B TyAlpha.hyps(3,4,5) lmap_ty_inv_inv
      lsubst_ty_def map_fst_zip map_snd_zip zip_commute)
  then have P16: "ty' = TArrow ty1 ty2 (map (lsubst (zip ys' xs')) zs)"
    by (simp add: lsubst_ty_def)

  show ?case
    using P16 P9 TyAlpha.IH by blast
next
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
  case (TyCase \<Gamma> P e0 ty1 \<Gamma>2 e1 ty2 e2 T)
  then show ?case
  by auto
next
  case (TyLIIntro lhs rhs P \<Gamma>)
  obtain i C zs fusions taus where
    prod_rhs: "rhs = (i, (C, zs), fusions, taus)"
  by (metis prod.collapse)
  obtain a vs where
    prod_lhs: "lhs = (a, vs)"
  by (metis prod.collapse)
  have P1: "make_LI (lhs, rhs) = TLI (mset taus) a vs (fset_of_list zs |\<union>| FLfusion_fset fusions)"
    using prod_rhs prod_lhs make_LI_def by simp
  then show ?case
    by (simp add: TyLIIntro.prems(1))
next
  case (TyLITrans \<Gamma> P T1 a2 xs2 tys1 a1 xs1 ys1 T2 tys2 ys2 ys)
  then show ?case
  apply auto
  done
next
  case (TyLIElim0 ys ys' xs T \<Gamma> P a)
  then show ?case
  apply auto
  done
next
  case (TyLIIntro0 \<Gamma> P T a xs)
  then show ?case
  apply auto
  done
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
next
  case (TyLIIntro lhs rhs P \<Gamma>)
  then show ?case 
  by (simp add: typing.TyLIIntro)
next
  case (TyLITrans \<Gamma> P T1 a2 xs2 tys1 a1 xs1 ys1 T2 tys2 ys2 ys)
  then show ?case 
  by (simp add: typing.TyLITrans)
next
  case (TyLIElim0 ys ys' xs T \<Gamma> P a)
  then show ?case 
  by (simp add: typing.TyLIElim0)
next
  case (TyLIIntro0 \<Gamma> P T a xs)
  then show ?case 
  by (simp add: typing.TyLIIntro0)
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
next
  case (TyLIIntro lhs rhs P \<Gamma>)
  then show ?case 
  apply auto
  done
next
  case (TyLITrans \<Gamma> P T1 a2 xs2 tys1 a1 xs1 ys1 T2 tys2 ys2 ys)
  then show ?case 
  apply auto
  done
next
  case (TyLIElim0 ys ys' xs T \<Gamma> P a)
  then show ?case 
  apply auto
  done
next
  case (TyLIIntro0 \<Gamma> P T a xs)
  then show ?case 
  apply auto
  done
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


lemma LI_isnot_Arrow:
  "make_LI (lhs, rhs) \<noteq> TArrow ty1 ty2 zs"
proof -
  obtain i C zs fusions taus where
    prod_rhs: "rhs = (i, (C, zs), fusions, taus)"
  by (metis prod.collapse)
  obtain a vs where
    prod_lhs: "lhs = (a, vs)"
  by (metis prod.collapse)
  show ?thesis
    by (simp add: make_LI_def prod_rhs prod_lhs)
qed

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
  case (TyAlpha \<Gamma>2 P g' ty xs' ys')
  have P1: "is_val (Graph g')"
    using TyAlpha.prems(1) is_graph_val_ignore_lmap is_val.simps(1) by blast
  then show ?case
  apply auto
  by (metis (no_types, lifting) ext A4 P1 TyAlpha.hyps(2,3,4,5,6)
    TyAlpha.prems(2,3) exp.inject(1) lmap.simps(2) lmap_graph_cong
    lmap_ty.simps(2) lmap_ty_inv_inv lsubst_ty_def map_eq_map_tailrec
    map_fst_zip map_snd_zip subset_code(1) zip_commute) (* 557 ms *) 
next
  case (TyCase \<Gamma> P e0 ty1 \<Gamma>2 e1 ty2 e2 T)
  then show ?case
  apply auto
  done
next
  case (TyLIIntro lhs rhs P \<Gamma>)
  then show ?case 
  by (simp add: LI_isnot_Arrow)
next
  case (TyLITrans \<Gamma> P T1 a2 xs2 tys1 a1 xs1 ys1 T2 tys2 ys2 ys)
  then show ?case 
  apply auto
  done
next
  case (TyLIElim0 ys ys' xs T \<Gamma> P a)
  then show ?case 
  apply auto
  done
next
  case (TyLIIntro0 \<Gamma> P T a xs)
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


lemma diffgraph_is_val:
  "is_graph_val (make_diffgraph rhs)"
proof -
  obtain i C zs fusions taus where
    prod_rhs: "rhs = (i, (C, zs), fusions, taus)"
  by (metis prod.collapse)

  have P1: "make_diffgraph rhs = 
    Mols1 (Atom (GConstr C) zs) (fusions_of fusions)"
    using prod_rhs make_diffgraph_def apply simp
    done

  have P2: "is_graph_val (Mols1 (Atom (GConstr C) zs) (fusions_of fusions))"
    using Mols1_is_val fusions_is_val is_atom_val.simps(1)
      is_graph_val.simps(2) by blast
  have P2: "is_graph_val (make_diffgraph rhs)"
    by (simp add: P1 P2)

  then show ?thesis .
qed


lemma is_val_lbinds_commute:
  "is_val (Graph T) = is_val (Graph (lbinds xs T))"
apply (simp add: lbinds_def)
proof (induct xs arbitrary: T)
  case Nil
  then show ?case 
  apply auto
  done
next
  case (Cons a xs)
  then show ?case 
  apply (simp add: lbind_def)
  by (simp add: is_graph_val_ignore_lmap)
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
next
  case (TyLIIntro lhs rhs P \<Gamma>)
  then show ?case 
  apply auto
  by (simp add: diffgraph_is_val)
next
  case (TyLITrans \<Gamma> P T1 a2 xs2 tys1 a1 xs1 ys1 T2 tys2 ys2 ys)
  then show ?case 
  apply auto
  done
next
  case (TyLIElim0 ys ys' xs T \<Gamma> P a)
  then show ?case 
  by (meson cbv_ty_GraphE is_val_lbinds_commute)
next
  case (TyLIIntro0 \<Gamma> P T a xs)
  then show ?case 
  apply auto
  done
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


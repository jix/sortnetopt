theory Huffman
  imports Main "HOL-Library.Multiset"
begin

text \<open>In this theory we define Huffman's algorithm and prove its correctness for an arbitrary
Huffman algebra (TODO ref). If you are only interested in the parts specific to sorting networks,
you can skip this theory.\<close>


text \<open>First we state the axioms of a Huffman algebra:\<close>

class huffman_algebra =
  fixes combine :: "'a::linorder \<Rightarrow> 'a \<Rightarrow> 'a"  (infix \<open>\<diamondop>\<close> 70)
  assumes increasing: \<open>a \<le> a \<diamondop> b\<close>
  assumes commutative: \<open>a \<diamondop> b = b \<diamondop> a\<close>
  assumes medial: \<open>(a \<diamondop> b) \<diamondop> (c \<diamondop> d) = (a \<diamondop> c) \<diamondop> (b \<diamondop> d)\<close>
  assumes mono: \<open>a \<le> b \<Longrightarrow> a \<diamondop> c \<le> b \<diamondop> c\<close>
  assumes assoc_ineq: \<open>a \<le> c \<Longrightarrow> (a \<diamondop> b) \<diamondop> c \<le> a \<diamondop> (b \<diamondop> c)\<close>

text \<open>We need some additional lemmas about lists, finite multisets of list elements elements and
sorted lists of multiset elements.\<close>

text \<open>Removing the head of a list, removes the corresponding element from a multiset.\<close>

lemma mset_tl: \<open>xs \<noteq> [] \<Longrightarrow> mset (tl xs) = mset xs - {#hd xs#}\<close>
  by (cases xs; simp)


text \<open>The first element of a sorted list of multiset elements is the minimum element of a multiset
if the multiset is nonempty.\<close>

lemma hd_sorted_list_of_multiset:
  assumes \<open>A \<noteq> {#}\<close>
  shows \<open>hd (sorted_list_of_multiset A) = Min_mset A\<close>
  by (metis (no_types, lifting) Min_in Min_le antisym assms finite_set_mset hd_Cons_tl
      list.set_sel(1) mset.simps(1) mset_sorted_list_of_multiset set_ConsD set_mset_eq_empty_iff
      set_sorted_list_of_multiset sorted.simps(2) sorted_list_of_multiset_mset sorted_sort)

text \<open>We can remove the smallest element of a nonempty multiset by turning it into a sorted list,
and building a multiset of that lists's tail.\<close>

lemma mset_tl_sorted_list_of_multiset:
  assumes \<open>A \<noteq> {#}\<close>
  shows \<open>mset (tl (sorted_list_of_multiset A)) = A - {#Min_mset A#}\<close>
  by (metis assms hd_sorted_list_of_multiset mset.simps(1) mset_sorted_list_of_multiset mset_tl)

text \<open>If we have a sorted list, we can recover it from a multiset of its elements.\<close>

lemma unique_sorted_list_of_multiset:
  assumes \<open>mset xs = A\<close> \<open>sorted xs\<close>
  shows \<open>xs = sorted_list_of_multiset A\<close>
  using assms(1) assms(2) sorted_sort_id by fastforce

text \<open>The tail of a sorted list of multiset elements is the same as the sorted list of elements
after removing the minimal element.\<close>

lemma tl_sorted_list_of_multiset:
  assumes \<open>A \<noteq> {#}\<close>
  shows \<open>tl (sorted_list_of_multiset A) = sorted_list_of_multiset (A - {#Min_mset A#})\<close>
proof -
  have \<open>sorted (tl (sorted_list_of_multiset A))\<close>
    by (metis mset_sorted_list_of_multiset sorted_list_of_multiset_mset sorted_sort sorted_tl)
  thus ?thesis
    by (simp add: assms mset_tl_sorted_list_of_multiset unique_sorted_list_of_multiset)
qed

(***)

text \<open>We also need an alternative characterization of the minimum function.\<close>

lemma min_as_logic:
  \<open>min (a::'a::linorder) b = c \<longleftrightarrow> (a = c \<and> a \<le> b) \<or> (b = c \<and> b \<le> a)\<close>
  \<open>c = min (a::'a::linorder) b \<longleftrightarrow> (a = c \<and> a \<le> b) \<or> (b = c \<and> b \<le> a)\<close>
  unfolding min_def by auto

(***)

text \<open>Huffman's algorithm repeatedly combines values in a multiset using the Huffman algebra's
operator. To prove that the resulting value is minimal, we need to manipulate syntax trees of
expressions using that operator, which we define here.\<close>

datatype 'a expr =
  Val (the_Val: 'a) ("\<langle>_\<rangle>") |
  Op (left_subexpr: \<open>'a expr\<close>) (right_subexpr: \<open>'a expr\<close>) (infix "\<star>" 70)

abbreviation is_Op :: \<open>'a expr \<Rightarrow> bool\<close> where
  \<open>is_Op E \<equiv> \<not>is_Val E\<close>

text \<open>The set of values in an expression is always non-empty and finite.\<close>

lemma set_expr_nonempty[simp]: \<open>set_expr E \<noteq> {}\<close>
  by (induction E; auto)

lemma set_expr_finite[simp]: \<open>finite (set_expr E)\<close>
  by (induction E; auto)

text \<open>We can recursively evaluate an expression using the Huffman algebra's operator.\<close>

fun (in huffman_algebra) value_expr :: \<open>'a expr \<Rightarrow> 'a\<close> where
  \<open>value_expr \<langle>a\<rangle> = a\<close> |
  \<open>value_expr (E \<star> F) = value_expr E \<diamondop> value_expr F\<close>

text \<open>We can flatten an expression into a nonempty list of contained values.\<close>

abbreviation list_expr :: \<open>'a expr \<Rightarrow> 'a list\<close> where
  \<open>list_expr \<equiv> rec_expr (\<lambda>a. [a]) (\<lambda>_ _. (@))\<close>

lemma list_expr_nonempty[simp]: \<open>list_expr E \<noteq> []\<close>
  by (induction E; auto)

text \<open>With this we can count the number of values in the expression.\<close>

abbreviation count_expr :: \<open>'a expr \<Rightarrow> nat\<close> where
  \<open>count_expr E \<equiv> length (list_expr E)\<close>

lemma count_expr_ge1[simp]: \<open>count_expr E \<ge> 1\<close>
  by (simp add: Suc_leI)
  
lemma count_expr_Op: \<open>count_expr (E \<star> F) \<ge> 2\<close>
  using count_expr_ge1[of E] count_expr_ge1[of F]
  by (simp; linarith)

lemma is_Op_by_count: \<open>is_Op E = (count_expr E \<ge> 2)\<close>
  by (cases E; simp; insert count_expr_Op; auto)

lemma expr_from_list: \<open>list_expr E = [e] \<Longrightarrow> E = \<langle>e\<rangle>\<close>
  by (cases E; simp add: append_eq_Cons_conv)

text \<open>The number of values in an expression is also directly related to the size of an expression.
We get the size and several useful of its properties for free whenever we define an algebraic
datatype. With this we get corresponding useful properties also for the number of an expression's
values.\<close>

lemma count_expr_size: \<open>2 * count_expr E = Suc (size E)\<close>
  by (induction E; auto)

text \<open>We define the multiset of an expression's values via the list of values.\<close>

abbreviation mset_expr :: \<open>'a expr \<Rightarrow> 'a multiset\<close> where
  \<open>mset_expr E \<equiv> mset (list_expr E)\<close>

text \<open>There is a unique expression containing just one given value.\<close>

lemma expr_from_mset: \<open>mset_expr E = {# a #} \<Longrightarrow> E = \<langle>a\<rangle>\<close>
  by (simp add: expr_from_list)

text \<open>Ignoring the multiplicity of the multisets's values gives us the same set as the automatically
defined function for the set of values in an expression.\<close>

lemma set_mset_expr: \<open>set_mset (mset_expr E) = set_expr E\<close>
  by (induction E; simp)

text \<open>We define the head of an expression as the leftmost value in the syntax tree, and we do this
via flattening the expression to a list of values.\<close>

abbreviation hd_expr :: \<open>'a expr \<Rightarrow> 'a\<close> where
  \<open>hd_expr E \<equiv> hd (list_expr E)\<close>

text \<open>We get the minimum value in an expression as the minimum value of the set of its values.\<close>

definition Min_expr :: \<open>'a::linorder expr \<Rightarrow> 'a\<close> where
  \<open>Min_expr E \<equiv> Min (set_expr E)\<close>

text \<open>If the expression contains just one value, the minimum is that value.\<close>

lemma Min_expr_Val[simp]: \<open>Min_expr \<langle>a\<rangle> = a\<close>
  unfolding Min_expr_def
  by simp

text \<open>Otherwise the minimum value can be computed recursively.\<close>

lemma Min_expr_Op: \<open>Min_expr (L \<star> R) = min (Min_expr L) (Min_expr R)\<close>
  unfolding Min_expr_def
  by (simp add: Min_Un min_def)

text \<open>As the Huffman algebra operator is increasing in both arguments, the minimum value in an
expression is a lower bound for its evaluation.\<close>

lemma (in huffman_algebra) Min_expr_bound:
  \<open>Min_expr E \<le> value_expr E\<close>
  by (induction E; simp add: Min_expr_Op; insert increasing min.coboundedI1 order_trans; blast)

text \<open>If two expressions have the same multiset of values they contain the same minimum value.\<close>

lemma Min_expr_mset_cong: \<open>mset_expr E = mset_expr F \<Longrightarrow> Min_expr E = Min_expr F\<close>
  unfolding Min_expr_def set_mset_expr[symmetric] by simp

text \<open>The minimum value in an expression is also the minimum value of the multiset of its values.\<close>

lemma Min_expr_from_mset: \<open>Min_expr E = Min_mset (mset_expr E)\<close>
  unfolding Min_expr_def
  by (fold set_mset_expr; simp)

text \<open>We define the tail of an expression as the expression we get by removing the head if that is
possible. This is always possible as long as the expression contains one operator.\<close>

fun tl_expr :: \<open>'a expr \<Rightarrow> 'a expr\<close> where
  \<open>tl_expr \<langle>a\<rangle> = \<langle>a\<rangle>\<close> |
  \<open>tl_expr (\<langle>l\<rangle> \<star> R) = R\<close> |
  \<open>tl_expr ((L \<star> M) \<star> R) = tl_expr (L \<star> M) \<star> R\<close>

text \<open>If the expression contains an operator, the tail of the list of its values is the same as the
list of values of its tail.\<close>

lemma list_tl_expr: \<open>is_Op E \<Longrightarrow> list_expr (tl_expr E) = tl (list_expr E)\<close>
  by (induction E rule: tl_expr.induct; simp)

text \<open>If two expressions have the same head and the same multiset of values, their tails also have
the same multiset of values.\<close>

lemma same_mset_tl_from_same_mset_mset_hd:
  assumes \<open>hd_expr E = hd_expr F\<close> \<open>mset_expr E = mset_expr F\<close>
  shows \<open>mset_expr (tl_expr E) = mset_expr (tl_expr F)\<close>
proof (cases \<open>is_Op E\<close>)
  case True
  hence \<open>is_Op F\<close>
    using mset_eq_length[of \<open>list_expr E\<close> \<open>list_expr F\<close>]
      is_Op_by_count[of E] is_Op_by_count[of F] assms(2)
    by auto
  thus ?thesis
    using assms True
    by (subst (1 2) list_tl_expr; simp; subst (1 2) mset_tl; simp)
next
  case False
  then obtain e where \<open>E = \<langle>e\<rangle>\<close>
    using expr.exhaust_sel by force
  hence \<open>F = E\<close>
    using expr.exhaust_sel assms(2) expr_from_list by fastforce
  then show ?thesis
    by simp
qed


(***)

text \<open>Given any property of an expression, we can define a corresponding property that holds if the
given property holds for all subexpressions of an expression (including the expression itself).\<close>

inductive all_subexpr :: \<open>('a expr \<Rightarrow> bool) \<Rightarrow> 'a expr \<Rightarrow> bool\<close> where
  val: \<open>P \<langle>a\<rangle> \<Longrightarrow> all_subexpr P \<langle>a\<rangle>\<close> |
  op: \<open>\<lbrakk>P (L \<star> R); all_subexpr P L; all_subexpr P R\<rbrakk> \<Longrightarrow> all_subexpr P (L \<star> R)\<close>

declare all_subexpr.intros[intro] all_subexpr.cases[elim]

lemma all_subexpr_top: \<open>all_subexpr P E \<Longrightarrow> P E\<close>
  by auto

lemma all_subexpr_expand: \<open>all_subexpr P (L \<star> R) = (P (L \<star> R) \<and> all_subexpr P L \<and> all_subexpr P R)\<close>
  by auto

(***)

text \<open>An expression has a minimal head, if its head is the minimum of the contained values.\<close>

abbreviation Min_hd_expr :: \<open>'a::linorder expr \<Rightarrow> bool\<close> where
  \<open>Min_hd_expr E \<equiv> hd_expr E = Min_expr E\<close>

text \<open>If an expression has this property, so does its left subexpression.\<close>

lemma Min_hd_expr_left_subexpr: \<open>Min_hd_expr (L \<star> R) \<Longrightarrow> Min_hd_expr L\<close>
  by (induction L; auto simp add: Min_expr_Op min_as_logic)

text \<open>In that case the minimum value contained in the left subexpression is at least as small as the
minimum value contained in the right subexpression.\<close>

lemma Min_hd_expr_subexpr_ord: \<open>Min_hd_expr (L \<star> R) \<Longrightarrow> Min_expr L \<le> Min_expr R\<close>
  using Min_hd_expr_left_subexpr min.orderI by (fastforce simp add: Min_expr_Op)

text \<open>Hence to find the minimum value in an minimal head expression, we only need to look at the
left subexpression.\<close>

lemma Min_hd_expr_left_subexpr_Min: \<open>Min_hd_expr (L \<star> R) \<Longrightarrow> Min_expr (L \<star> R) = Min_expr L\<close>
  by (induction L; auto simp add: Min_expr_Op min_as_logic)

text \<open>If two minimal head expressions have the same head they have same minimum contained value.\<close>

lemma Min_hd_expr_Min_from_hd_cong:
  assumes \<open>Min_hd_expr E\<close> \<open>Min_hd_expr F\<close> \<open>hd_expr E = hd_expr F\<close>
  shows \<open>Min_expr E = Min_expr F\<close>
  using assms by simp

text \<open>To turn an expression into a minimal head expression without changing the value it evaluates
to, we can swap the sides of every operator where the right subexpression contains a smaller value
than the minimum value on the left.\<close>

text \<open>To do this we first define this function which combines two subexpressions such that the
minimum value is on the left.\<close>

function Min_to_hd_subexpr :: \<open>'a::linorder expr \<Rightarrow> 'a::linorder expr \<Rightarrow> 'a expr\<close> where
  \<open>Min_expr L \<le> Min_expr R \<Longrightarrow> Min_to_hd_subexpr L R = L \<star> R\<close> |
  \<open>\<not>(Min_expr L \<le> Min_expr R) \<Longrightarrow> Min_to_hd_subexpr L R = R \<star> L\<close>
  by auto
termination by lexicographic_order

text \<open>Doing this results in an expression with the same multiset of values as combining them in a
fixed order would result in.\<close>

lemma Min_to_hd_subexpr_mset: \<open>mset_expr (Min_to_hd_subexpr L R) = mset_expr (L \<star> R)\<close>
  by (cases \<open>(L, R)\<close> rule: Min_to_hd_subexpr.cases; auto)

text \<open>And does not change the value it evaluates to.\<close>

lemma (in huffman_algebra) value_Min_to_hd_subexpr:
  \<open>value_expr (Min_to_hd_subexpr L R) = value_expr L \<diamondop> value_expr R\<close>
  by (metis Min_to_hd_subexpr.simps commutative value_expr.simps(2))

text \<open>If we have two expressions, both for which all subexpression have a minimal head, combining
them this way results in an expression where still all subexpressions have a minimal head.\<close>

lemma Min_to_hd_subexpr_spec:
  assumes \<open>all_subexpr Min_hd_expr L\<close> \<open>all_subexpr Min_hd_expr R\<close>
  shows \<open>all_subexpr Min_hd_expr (Min_to_hd_subexpr L R)\<close>
proof (cases \<open>Min_expr L \<le> Min_expr R\<close>)
  case True
  have \<open>Min_expr (L \<star> R) = Min_expr L \<and> hd_expr (L \<star> R) = hd_expr L\<close>
    by (simp add: True Min_expr_Op min_def)
  hence \<open>Min_hd_expr (L \<star> R)\<close>
    using assms by auto 
  thus ?thesis
    using assms True by auto
next
  case False
  hence False': \<open>Min_expr R \<le> Min_expr L\<close>
    using linear by blast
  have \<open>Min_expr (R \<star> L) = Min_expr R \<and> hd_expr (R \<star> L) = hd_expr R\<close>
    by (auto simp add: False' Min_expr_Op min_def)
  hence \<open>Min_hd_expr (R \<star> L)\<close>
    using assms by auto 
  thus ?thesis
    using assms False by auto
qed

text \<open>Thus we can turn any expression into one with only minimal head subexpressions, by recursing
and combining subexpressions with @{term Min_to_hd_subexpr}.\<close>

fun Min_to_hd_expr :: \<open>'a::linorder expr \<Rightarrow> 'a expr\<close> where
  \<open>Min_to_hd_expr \<langle>a\<rangle> = \<langle>a\<rangle>\<close> |
  \<open>Min_to_hd_expr (L \<star> R) = Min_to_hd_subexpr (Min_to_hd_expr L) (Min_to_hd_expr R)\<close>

lemma Min_to_hd_expr_spec:
  \<open>all_subexpr Min_hd_expr (Min_to_hd_expr E)\<close>
  by (induction E rule: Min_to_hd_expr.induct;
      (subst Min_to_hd_expr.simps; rule Min_to_hd_subexpr_spec)?;
      auto)

text \<open>This does not change the multiset of values nor what the expression evaluates to.\<close>

lemma Min_to_hd_expr_mset: \<open>mset_expr (Min_to_hd_expr E) = mset_expr E\<close>
  by (induction E rule: Min_to_hd_expr.induct; simp add: Min_to_hd_subexpr_mset)

lemma (in huffman_algebra) value_Min_to_hd_expr:
  \<open>value_expr (Min_to_hd_expr E) = value_expr E\<close>
  by (induction E rule: Min_to_hd_expr.induct; simp add: value_Min_to_hd_subexpr)

(***)

text \<open>We also want an expression's tail to have a minimal head, such that the two smallest values
are the leftmost of an expression.\<close>

abbreviation tl_Min_hd_expr :: \<open>'a::linorder expr \<Rightarrow> bool\<close> where
  \<open>tl_Min_hd_expr E \<equiv> Min_hd_expr (tl_expr E)\<close>

text \<open>This property depends only on the list of elements, not on how they are nested.\<close>

lemma tl_Min_hd_expr_list_expr_cong:
  assumes \<open>list_expr E = list_expr F\<close>
  shows \<open>tl_Min_hd_expr E = tl_Min_hd_expr F\<close>
proof -
  have \<open>\<And>E. tl (list_expr E) = list_expr (tl_expr E) \<or> \<langle>the_Val E\<rangle> = E\<close>
    using expr.collapse(1) list_tl_expr by fastforce
  then have \<open>list_expr (tl_expr E) = list_expr (tl_expr F)\<close>
    using assms by (metis (no_types) expr.simps(7) expr_from_list)
  then show ?thesis
    by (metis Min_expr_mset_cong)
qed

text \<open>By going through several cases, we can rearrange subexpression to ensure that the minimum
value of the tail of an expression is in the left subexpression of an expression. We do this in a
way that the Huffman algebra axioms ensure that the evaluation result is not increased as long as
all subexpressions of the input have a minimal head.\<close>

function tl_Min_to_hd_subexpr :: \<open>'a::linorder expr \<Rightarrow> 'a expr\<close> where
  \<open>tl_Min_to_hd_subexpr \<langle>a\<rangle> = \<langle>a\<rangle>\<close> |
  \<open>tl_Min_to_hd_subexpr (\<langle>l\<rangle> \<star> R) = \<langle>l\<rangle> \<star> R\<close> |
  \<open>Min_expr M \<le> r \<Longrightarrow>
    tl_Min_to_hd_subexpr ((L \<star> M) \<star> \<langle>r\<rangle>) = (L \<star> M) \<star> \<langle>r\<rangle>\<close> |
  \<open>\<not>(Min_expr M \<le> r) \<Longrightarrow>
    tl_Min_to_hd_subexpr ((L \<star> M) \<star> \<langle>r\<rangle>) = (L \<star> \<langle>r\<rangle>) \<star> M\<close> |
  \<open>Min_expr LM \<le> Min_expr RM \<Longrightarrow>
    tl_Min_to_hd_subexpr ((L \<star> LM) \<star> (RM \<star> R)) = (L \<star> LM) \<star> (RM \<star> R)\<close> |
  \<open>\<not>(Min_expr LM \<le> Min_expr RM) \<Longrightarrow>
    tl_Min_to_hd_subexpr ((L \<star> LM) \<star> (RM \<star> R)) = (L \<star> RM) \<star> (LM \<star> R)\<close>
  by (auto, metis tl_expr.cases)
termination by lexicographic_order

text \<open>We show that it does not change the size.\<close>

lemma tl_Min_to_hd_subexpr_size[simp]:
  \<open>size (tl_Min_to_hd_subexpr E) = size E\<close>
  by (induction E rule: tl_Min_to_hd_subexpr.induct; simp)

text \<open>Which allows us to apply it while recursing on the result of that application.\<close>

fun tl_Min_to_hd_expr :: \<open>'a::linorder expr \<Rightarrow> 'a expr\<close>
  and helper_tl_Min_to_hd_expr :: \<open>'a::linorder expr \<Rightarrow> 'a expr\<close> where
    \<open>tl_Min_to_hd_expr E = helper_tl_Min_to_hd_expr (tl_Min_to_hd_subexpr E) \<close> |
    \<open>helper_tl_Min_to_hd_expr \<langle>a\<rangle> = \<langle>a\<rangle>\<close> |
    \<open>helper_tl_Min_to_hd_expr (L \<star> R) = tl_Min_to_hd_expr L \<star> R\<close>

text \<open>This recursion also does not change the multiset of values, the minimum value, the head, the
multiset of tail values or the minimum value of the tail.\<close>

lemma tl_Min_to_hd_expr_mset: \<open>mset_expr (tl_Min_to_hd_expr E) = mset_expr E\<close>
proof (induction \<open>size E\<close> arbitrary: E rule: less_induct)
  case less
  then show ?case
    by (cases E rule: tl_Min_to_hd_subexpr.cases; simp)
qed


lemma tl_Min_to_hd_expr_Min: \<open>Min_expr (tl_Min_to_hd_expr E) = Min_expr E\<close>
  using tl_Min_to_hd_expr_mset[of E]
  unfolding Min_expr_def set_mset_expr[symmetric]
  by simp

lemma tl_Min_to_hd_expr_hd: \<open>hd_expr (tl_Min_to_hd_expr E) = hd_expr E\<close>
proof (induction \<open>size E\<close> arbitrary: E rule: less_induct)
  case less
  then show ?case
    by (cases E rule: tl_Min_to_hd_subexpr.cases; simp)
qed

lemma tl_Min_to_hd_expr_mset_tl: \<open>mset_expr (tl_expr (tl_Min_to_hd_expr E)) = mset_expr (tl_expr E)\<close>
  by (subst same_mset_tl_from_same_mset_mset_hd[of E \<open>tl_Min_to_hd_expr E\<close>];
      simp add: tl_Min_to_hd_expr_hd tl_Min_to_hd_expr_mset del: tl_Min_to_hd_expr.simps)

lemma tl_Min_to_hd_expr_Min_tl: \<open>Min_expr (tl_expr (tl_Min_to_hd_expr E)) = Min_expr (tl_expr E)\<close>
  using Min_expr_mset_cong tl_Min_to_hd_expr_mset_tl by blast

text \<open>To further analyze @{term tl_Min_to_hd_subexpr}, we need various lemmas about minimum
contained values and minimal head values for expressions and tails of expressions and how they
relate when rearranging subexpressions.\<close>

text \<open>Given a minimal head expression, if we rewrite the left subexpression without changing the
minimum value or the head, we still have a minimal head expression.\<close>

lemma Min_hd_expr_rewrite_left:
  assumes \<open>Min_hd_expr (L \<star> R)\<close> \<open>Min_expr L = Min_expr L'\<close> \<open>Min_hd_expr L'\<close>
  shows \<open>Min_hd_expr (L' \<star> R)\<close>
  by (metis (mono_tags, lifting)
      Min_expr_Op Min_hd_expr_left_subexpr assms expr.simps(8) hd_append2 list_expr_nonempty)

text \<open>If we have a minimal head expression and exchange the right subexpression with the right
subexpression of the left subexpression, we still have a minimal head expression.\<close>

lemma Min_hd_expr_exchange_right:
  assumes \<open>Min_hd_expr ((L \<star> M) \<star> R)\<close>
  shows \<open>Min_hd_expr ((L \<star> R) \<star> M)\<close>
  using assms
  by (simp add: Min_expr_Op; metis min.commute min.assoc)

text \<open>This extends to all minimal head subexpressions.\<close>

lemma all_subexpr_Min_hd_expr_exchange_right:
  assumes \<open>all_subexpr Min_hd_expr ((L \<star> M) \<star> R)\<close>
  shows \<open>all_subexpr Min_hd_expr ((L \<star> R) \<star> M)\<close>
  by (intro all_subexpr.op; insert assms Min_hd_expr_exchange_right Min_hd_expr_left_subexpr; blast)

text \<open>Combining an expression where the tail has a minimal head with a singleton expression still
has a tail with a minimal head, if that singleton expression is larger than the tail's minimal
head.\<close>

lemma tl_Min_hd_expr_right_Val:
  assumes \<open>tl_Min_hd_expr L\<close> \<open>Min_expr (tl_expr L) \<le> r\<close>
  shows \<open>tl_Min_hd_expr (L \<star> \<langle>r\<rangle>)\<close>
  using assms
  by (cases L; simp add: Min_expr_Op min_absorb1 dual_order.trans min_def_raw)

text \<open>If we have an upper bound for the minimum value in an expression, combining it with another
expression on the left and then taking the tail of the resulting expression results in an expression
that still has that upper bound, as it still contains all values of our initial expression.\<close>

lemma Min_expr_tl_bound:
  assumes \<open>Min_expr M \<le> r\<close>
  shows \<open>Min_expr (tl_expr (L \<star> M)) \<le> r\<close>
  using assms
  by (cases L; simp add: Min_expr_Op min_le_iff_disj)

text \<open>If we have a nonsingleton expression whose tail has a minimal head, combining it with another
expression on the right whose minimal value is not smaller than the left expression's tail's minimal
head, is an expression whose tail again has a minimal head.\<close>

lemma tl_Min_hd_expr_right:
  assumes \<open>is_Op L\<close> \<open>tl_Min_hd_expr L\<close> \<open>Min_expr (tl_expr L) \<le> Min_expr R\<close>
  shows \<open>tl_Min_hd_expr (L \<star> R)\<close>
  using assms
  by (cases L; simp add: Min_expr_Op min_absorb1 dual_order.trans min_def_raw)

text \<open>Applying @{term tl_Min_to_hd_expr} to a non-singleton expression results in a non-singleton
expression.\<close>

lemma is_Op_tl_Min_to_hd_expr: \<open>is_Op (tl_Min_to_hd_expr (L \<star> R))\<close>
  unfolding is_Op_by_count
  by (metis (mono_tags, lifting) count_expr_Op mset_eq_length tl_Min_to_hd_expr_mset)

text \<open>If we have an expression where all subexpressions have a minimal head, applying @{term
tl_Min_to_hd_expr} results in an expression where the tail has a minimal head.\<close>

lemma tl_Min_to_hd_expr_spec:
  \<open>all_subexpr Min_hd_expr E \<Longrightarrow> tl_Min_hd_expr (tl_Min_to_hd_expr E)\<close>
proof (induction \<open>size E\<close> arbitrary: E rule: less_induct)
case less
  then show ?case 
  proof (cases E rule: tl_Min_to_hd_subexpr.cases; (auto; fail)?)
    case (3 M r L)

    have A: \<open>all_subexpr Min_hd_expr (L \<star> M)\<close>
      using 3 less.prems by blast

    have B: \<open>Min_expr (tl_expr (tl_Min_to_hd_expr (L \<star> M))) \<le> r\<close>
      by (subst tl_Min_to_hd_expr_Min_tl; rule Min_expr_tl_bound; simp add: 3)

    show ?thesis
      by (simp add: 3; fold tl_Min_to_hd_expr.simps;
          rule tl_Min_hd_expr_right_Val; insert 3 A B less; auto)
  next
    case (4 M r L)

    have \<open>all_subexpr Min_hd_expr (L \<star> \<langle>r\<rangle>)\<close>
      using 4 less.prems all_subexpr_Min_hd_expr_exchange_right by fastforce 
    hence A: \<open>tl_Min_hd_expr (tl_Min_to_hd_expr (L \<star> \<langle>r\<rangle>))\<close>
      using 4 less.hyps by auto

    have B: \<open>Min_expr (tl_expr (tl_Min_to_hd_expr (L \<star> \<langle>r\<rangle>))) \<le> Min_expr M\<close>
      by (subst tl_Min_to_hd_expr_Min_tl; metis "4"(1) Min_expr_Val Min_expr_tl_bound linear)

    show ?thesis 
      by (simp add: 4; fold tl_Min_to_hd_expr.simps; rule tl_Min_hd_expr_right;
          insert is_Op_tl_Min_to_hd_expr A B; simp)
  next
    case (5 LM RM L R)

    have A: \<open>tl_Min_hd_expr (tl_Min_to_hd_expr (L \<star> LM))\<close>
      using 5 less by auto

    have *: \<open>Min_expr LM \<le> Min_expr RM \<and> Min_expr LM \<le> Min_expr R\<close>
      using less.prems unfolding 5
      by (simp add: all_subexpr_expand Min_expr_Op;
          insert 5 all_subexpr_top order_trans; auto simp add: min_as_logic)

    have B: \<open>Min_expr (tl_expr (tl_Min_to_hd_expr (L \<star> LM))) \<le> Min_expr (RM \<star> R)\<close>
      by (subst tl_Min_to_hd_expr_Min_tl; rule Min_expr_tl_bound; simp add: * Min_expr_Op)

    show ?thesis
      by (simp add: 5; fold tl_Min_to_hd_expr.simps; rule tl_Min_hd_expr_right;
          insert is_Op_tl_Min_to_hd_expr A B; simp)
  next
    case (6 LM RM L R)

    have *: \<open>Min_expr L \<le> Min_expr RM\<close>
      using less.prems unfolding 6
      by (simp add: all_subexpr_expand Min_expr_Op; insert all_subexpr_top min.orderI; fastforce)
      
    have **: \<open>all_subexpr Min_hd_expr (L \<star> RM)\<close>
      by (rule all_subexpr.op; insert * 6 less.prems; auto simp add: Min_expr_Op min_def)

    have A: \<open>tl_Min_hd_expr (tl_Min_to_hd_expr (L \<star> RM))\<close>
      using ** less 6 by auto

    have ***: \<open>Min_expr RM \<le> Min_expr LM \<and> Min_expr RM \<le> Min_expr R\<close>
      using less.prems unfolding 6
      by (simp add: all_subexpr_expand Min_expr_Op;
          insert 6 all_subexpr_top min.orderI; force)

    have B: \<open>Min_expr (tl_expr (tl_Min_to_hd_expr (L \<star> RM))) \<le> Min_expr (LM \<star> R)\<close>
      by (subst tl_Min_to_hd_expr_Min_tl; rule Min_expr_tl_bound; simp add: *** Min_expr_Op)

    show ?thesis
      by (simp add: 6; fold tl_Min_to_hd_expr.simps; rule tl_Min_hd_expr_right;
          insert is_Op_tl_Min_to_hd_expr A B; auto)
  qed
qed

text \<open>If we have an expression where all subexpressions have a minimal head, applying @{term
tl_Min_to_hd_expr} also does not increase the evaluation result.\<close>

lemma (in huffman_algebra) value_tl_Min_to_hd_expr:
  \<open>all_subexpr Min_hd_expr E \<Longrightarrow> value_expr (tl_Min_to_hd_expr E) \<le> value_expr E\<close>
proof (induction \<open>size E\<close> arbitrary: E rule: less_induct)
  case less
  then show ?case
  proof (cases E rule: tl_Min_to_hd_subexpr.cases; (auto; fail)?)
    case (3 M r L)
    show ?thesis
      by (simp add: 3; fold tl_Min_to_hd_expr.simps; metis (no_types, lifting) "3"(2) add_Suc_right
          all_subexpr_expand dual_order.strict_trans2 expr.size(4) huffman_algebra.mono
          huffman_algebra_axioms le_add1 less.hyps less.prems lessI value_expr.simps(2))
  next
    case (4 M r L)

    have *: \<open>value_expr ((L \<star> \<langle>r\<rangle>) \<star> M) \<le> value_expr ((L \<star> M) \<star> \<langle>r\<rangle>)\<close>
      by (simp; metis "4"(1) assoc_ineq commutative huffman_algebra.Min_expr_bound
          huffman_algebra_axioms linear order_trans)

    have **: \<open>value_expr (tl_Min_to_hd_expr (L \<star> \<langle>r\<rangle>)) \<le> value_expr (L \<star> \<langle>r\<rangle>)\<close>
      by (metis (mono_tags, lifting) "4"(1) "4"(2) add.right_neutral add_Suc_right
          all_subexpr_Min_hd_expr_exchange_right all_subexpr_expand expr.size(4) le_add1
          le_imp_less_Suc less.hyps less.prems tl_Min_to_hd_subexpr.simps(4)
          tl_Min_to_hd_subexpr_size)

    show ?thesis
      by (simp add: 4; fold tl_Min_to_hd_expr.simps; insert * **; simp add: dual_order.trans mono) 
  next
    case (5 LM RM L R)
    show ?thesis
      by (simp add: 5; fold tl_Min_to_hd_expr.simps; metis (no_types, lifting) "5"(2) Suc_le_eq
          add.right_neutral add_Suc_right all_subexpr_expand expr.size(4) le_add1 less.hyps
          less.prems mono order.strict_iff_order value_expr.simps(2))
  next
    case (6 LM RM L R)

    have *: \<open>value_expr ((L \<star> LM) \<star> (RM \<star> R)) = value_expr ((L \<star> RM) \<star> (LM \<star> R))\<close>
      by (simp add: medial)

    have \<open>all_subexpr Min_hd_expr (L \<star> RM)\<close>
      using less unfolding 6 all_subexpr_expand
      by (metis (mono_tags, lifting) Min_expr_Op Min_hd_expr_left_subexpr_Min expr.simps(8)
          hd_append2 list_expr_nonempty)

    hence **: \<open>value_expr (tl_Min_to_hd_expr (L \<star> RM)) \<le> value_expr (L \<star> RM)\<close>
      by (metis (no_types, lifting) "6"(1) "6"(2) add.right_neutral add_Suc_right expr.size(4)
          le_add1 le_imp_less_Suc less.hyps tl_Min_to_hd_subexpr.simps(6) tl_Min_to_hd_subexpr_size)

    show ?thesis
      by (simp add: 6; fold tl_Min_to_hd_expr.simps; insert * **; simp add: mono)
  qed
qed

(***)

text \<open>At this point we can move the two smallest values of an expression to the very left without
increasing its value. To show that we can always combine the smallest two values, we now need to
make sure that the leftmost nonsingleton subexpression combines two singleton subexpression, i.e.\
combines two values.\<close>

inductive left_nested_expr :: \<open>'a expr \<Rightarrow> bool\<close> where
  pair: \<open>left_nested_expr (\<langle>l\<rangle> \<star> \<langle>r\<rangle>)\<close> |
  nested: \<open>left_nested_expr L \<Longrightarrow> left_nested_expr (L \<star> R)\<close>

text \<open>Whenever we have a singleton subexpression on the left, but not on the right, we can perform a
rotation that splits the nonsingleton right subexpression.\<close>

fun nest_left_subexpr :: \<open>'a::linorder expr \<Rightarrow> 'a expr\<close> where
  \<open>nest_left_subexpr \<langle>a\<rangle> = \<langle>a\<rangle>\<close> |
  \<open>nest_left_subexpr (\<langle>l\<rangle> \<star> \<langle>r\<rangle>) = (\<langle>l\<rangle> \<star> \<langle>r\<rangle>)\<close> |
  \<open>nest_left_subexpr (\<langle>l\<rangle> \<star> (M \<star> R)) = (\<langle>l\<rangle> \<star> M) \<star> R\<close> |
  \<open>nest_left_subexpr ((L \<star> M) \<star> R) = ((L \<star> M) \<star> R)\<close>

text \<open>This does not change the expression's size or multiset of values.\<close>

lemma nest_left_subexpr_size[simp]:
  \<open>size (nest_left_subexpr E) = size E\<close>
  by (induction E rule: nest_left_subexpr.induct; simp)

lemma nest_left_subexpr_mset[simp]:
  \<open>mset_expr (nest_left_subexpr E) = mset_expr E\<close>
  by (induction E rule: nest_left_subexpr.induct; simp)

text \<open>We can perform such rotations and then recurse on the left subexpression of the result. \<close>

fun nest_left_expr :: \<open>'a::linorder expr \<Rightarrow> 'a expr\<close>
  and helper_nest_left_expr :: \<open>'a::linorder expr \<Rightarrow> 'a expr\<close> where
    \<open>nest_left_expr E = helper_nest_left_expr (nest_left_subexpr E) \<close> |
    \<open>helper_nest_left_expr \<langle>a\<rangle> = \<langle>a\<rangle>\<close> |
    \<open>helper_nest_left_expr (L \<star> R) = nest_left_expr L \<star> R\<close>

text \<open>Rotations don't change the list order of values.\<close>

lemma nest_left_expr_list: \<open>list_expr (nest_left_expr E) = list_expr E\<close>
proof (induction \<open>size E\<close> arbitrary: E rule: less_induct)
  case less
  then show ?case
    by (cases E rule: nest_left_subexpr.cases; simp)
qed

declare left_nested_expr.intros[intro] left_nested_expr.cases[elim]

text \<open>Performing these rotations results in an expression that has the wanted property of directly
combining the leftmost value with another value.\<close>

lemma left_nested_nest_left_expr:
  \<open>is_Op E \<Longrightarrow> left_nested_expr (nest_left_expr E)\<close>
proof (induction \<open>size E\<close> arbitrary: E rule: less_induct)
  case less
  then show ?case
    by (cases E rule: nest_left_subexpr.cases; auto)
qed

text \<open>If the initial expression has a minimal head, these rotations also do not increase the
evaluation result.\<close>

lemma (in huffman_algebra) value_nest_left_expr:
  \<open>\<lbrakk>Min_hd_expr E\<rbrakk> \<Longrightarrow> value_expr (nest_left_expr E) \<le> value_expr E\<close>
proof (induction \<open>size E\<close> arbitrary: E rule: less_induct)
  case less
  then show ?case
  proof (cases E rule: nest_left_subexpr.cases; (auto; fail)?)
    case (3 l M R)

    have A: \<open>l \<le> Min_expr M\<close>
      by (metis "3" Min_expr_Op Min_expr_Val Min_hd_expr_subexpr_ord less.prems min.bounded_iff)
    hence \<open>Min_hd_expr (\<langle>l\<rangle> \<star> M)\<close> \<open>size (\<langle>l\<rangle> \<star> M) < size E\<close>
      by (auto simp add: Min_expr_Op min.absorb1 3)
    hence \<open>value_expr (nest_left_expr (\<langle>l\<rangle> \<star> M)) \<le> value_expr (\<langle>l\<rangle> \<star> M)\<close>
      using less.hyps by fastforce
    hence *: \<open>value_expr (nest_left_expr (\<langle>l\<rangle> \<star> M) \<star> R) \<le> value_expr ((\<langle>l\<rangle> \<star> M) \<star> R)\<close>
      by (simp add: mono)

    have \<open>l \<le> Min_expr R\<close>
      by (metis "3" Min_expr_Op Min_expr_Val Min_hd_expr_left_subexpr_Min less.prems
          min.cobounded2 min_le_iff_disj)
    hence **: \<open>value_expr ((\<langle>l\<rangle> \<star> M) \<star> R) \<le> value_expr (\<langle>l\<rangle> \<star> (M \<star> R))\<close>
      using A
      by (metis Min_expr_bound assoc_ineq order_trans value_expr.simps(1) value_expr.simps(2))

    show ?thesis 
      by (simp add: 3; fold nest_left_expr.simps; insert * **; auto)
  next
    case (4 L M R)
    show ?thesis
      by (simp add: 4; fold nest_left_expr.simps; metis "4" Min_hd_expr_left_subexpr Suc_le_eq
          add.right_neutral add_Suc_right dual_order.strict_iff_order expr.size(4) le_add1
          less.hyps less.prems mono value_expr.simps(2))
  qed
qed


(***)

text \<open>We now combine our three rearrangement steps: first we swap left and right subexpressions
whenever the right subexpression contains a smaller value, then we rearrange subexpressions to move
the second smallest value to the second position from the left and finally we perform tree rotations
to pair up the two smallest values.\<close>

definition rearrange_expr :: \<open>'a::linorder expr \<Rightarrow> 'a expr\<close> where
   \<open>rearrange_expr E = nest_left_expr (tl_Min_to_hd_expr (Min_to_hd_expr E))\<close>

text \<open>As intended, the result has the same multiset of values, still has a minimal head and a tail
with minimal head and does have the two leftmost values in the leftmost nonsingleton subexpression.\<close>

lemma rearrange_expr_mset: \<open>mset_expr (rearrange_expr E) = mset_expr E\<close>
  by (metis Min_to_hd_expr_mset nest_left_expr_list rearrange_expr_def tl_Min_to_hd_expr_mset)

lemma Min_hd_rearrange_expr: \<open>Min_hd_expr (rearrange_expr E)\<close>
  by (metis (mono_tags, lifting) Min_expr_mset_cong Min_to_hd_expr_spec all_subexpr_top
      nest_left_expr_list rearrange_expr_def tl_Min_to_hd_expr_Min tl_Min_to_hd_expr_hd)

lemma tl_Min_hd_rearrange_expr: \<open>tl_Min_hd_expr (rearrange_expr E)\<close>
  unfolding rearrange_expr_def
  using tl_Min_to_hd_expr_spec Min_to_hd_expr_spec nest_left_expr_list tl_Min_hd_expr_list_expr_cong
  by blast

lemma left_nested_rearrange_expr:
  assumes \<open>is_Op E\<close>
  shows \<open>left_nested_expr (rearrange_expr E)\<close>
proof -
  have \<open>is_Op (tl_Min_to_hd_expr (Min_to_hd_expr E))\<close>
    using assms unfolding is_Op_by_count
    by (metis (mono_tags, lifting) Min_to_hd_expr_mset mset_eq_length tl_Min_to_hd_expr_mset)
  thus ?thesis
    unfolding rearrange_expr_def
    using left_nested_nest_left_expr by blast
qed

text \<open>All this combined also does not increase the evaluation result.\<close>

lemma (in huffman_algebra) value_rearrange_expr:
  \<open>value_expr (rearrange_expr E) \<le> value_expr E\<close>
  unfolding rearrange_expr_def
  by (metis (mono_tags, lifting) Min_to_hd_expr_spec all_subexpr_top order_trans
      tl_Min_to_hd_expr_Min tl_Min_to_hd_expr_hd value_Min_to_hd_expr value_nest_left_expr
      value_tl_Min_to_hd_expr)

(***)

text \<open>For an expression with a minimal head, the head value is the head of the sorted list of its
values, which is the minimal value.\<close>

lemma Min_hd_expr_sorted_1:
  \<open>Min_hd_expr E \<Longrightarrow> hd_expr E = hd (sorted_list_of_multiset (mset_expr E))\<close>
  by (metis Min_expr_from_mset hd_sorted_list_of_multiset length_0_conv list_expr_nonempty
      mset.simps(1) size_mset)

text \<open>For an expression with a minimal head and a tail with minimal head, the head value of its
tail is the second value in the sorted list of its values, which is the second smallest value.\<close>

lemma Min_hd_expr_sorted_2:
  assumes \<open>is_Op E\<close> \<open>Min_hd_expr E\<close> \<open>tl_Min_hd_expr E\<close>
  shows \<open>hd_expr (tl_expr E) = hd (tl (sorted_list_of_multiset (mset_expr E)))\<close>
  by (metis Min_expr_from_mset Min_hd_expr_sorted_1 assms list_expr_nonempty
      list_tl_expr mset_tl mset_zero_iff tl_sorted_list_of_multiset)

text \<open>From this we get that the head the result of rearranging an expression is the minimal value of
the initial expression.\<close>

lemma hd_list_rearrange_expr:
  \<open>hd_expr (rearrange_expr E) = hd (sorted_list_of_multiset (mset_expr E))\<close>
  by (metis Min_expr_from_mset Min_hd_rearrange_expr hd_sorted_list_of_multiset list_expr_nonempty
      mset_zero_iff rearrange_expr_mset)

text \<open>We also get that the second leftmost value in the rearranged expression is the second smallest
value of the initial expression.\<close>

lemma hd_tl_list_rearrange_expr:
  \<open>hd (tl (list_expr (rearrange_expr E))) = hd (tl (sorted_list_of_multiset (mset_expr E)))\<close>
  by (cases E; (simp add: rearrange_expr_def; fail)?; simp;
      metis (mono_tags, lifting) Min_hd_expr_sorted_2 Min_hd_rearrange_expr count_expr_Op
      expr.simps(8) is_Op_by_count list_tl_expr mset_append mset_eq_length rearrange_expr_mset
      tl_Min_hd_rearrange_expr)

text \<open>If two lists have the same length and they match on their first two entries, the have the same
length-2 prefix.\<close>

lemma take_2_from_hds:
  assumes \<open>length xs = length ys\<close> \<open>hd xs = hd ys\<close> \<open>hd (tl xs) = hd (tl ys)\<close>
  shows \<open>take 2 xs = take 2 ys\<close>
  using assms
  by (cases xs; simp; cases ys; simp; cases \<open>tl xs\<close>; simp; cases \<open>tl ys\<close>; simp)

text \<open>This allows us to state that the leftmost two values of a rearranged expression are the two
smallest values.\<close>

lemma take_2_list_rearrange_expr:
  \<open>take 2 (list_expr (rearrange_expr E)) = take 2 (sorted_list_of_multiset (mset_expr E))\<close>
  by (rule take_2_from_hds; (simp add: hd_list_rearrange_expr hd_tl_list_rearrange_expr; fail)?;
      metis mset_sorted_list_of_multiset rearrange_expr_mset size_mset)


(***)

text \<open>We want to replace the subexpression of the two smallest values. For this we first inductively
define what it means for an expression to have a subexpression.\<close>

inductive has_subexpr :: \<open>'a expr \<Rightarrow> 'a expr \<Rightarrow> bool\<close> where
  here: \<open>has_subexpr X X\<close> |
  left: \<open>has_subexpr X L \<Longrightarrow> has_subexpr X (L \<star> R)\<close> |
  right: \<open>has_subexpr X R \<Longrightarrow> has_subexpr X (L \<star> R)\<close>

declare has_subexpr.intros[intro] has_subexpr.cases[elim]

lemma has_subexpr_simp_Op:
  \<open>has_subexpr E (L \<star> R) = (E = L \<star> R \<or> has_subexpr E L \<or> has_subexpr E R)\<close>
  by blast

text \<open>Any value present in an expression corresponds to a present subexpression consisting of just
that value.\<close>

lemma has_subexpr_Val: \<open>a \<in> set_expr E = has_subexpr \<langle>a\<rangle> E\<close>
  by (induction E; auto)

text \<open>The multiset of values in a subexpression is a subset of the multiset of the values of the
whole expression.\<close>

lemma mset_has_subexpr: \<open>has_subexpr X E \<Longrightarrow> mset_expr X \<subseteq># mset_expr E\<close>
  by (induction E; auto; insert subset_mset.add_increasing subset_mset.add_increasing2; fastforce)

text \<open>For an expression where the two leftmost values are combined (@{term left_nested_expr}}, the
subexpression that combines those terms is indeed a subexpression.\<close>

lemma left_nested_expr_has_hd2_subexpr:
  assumes \<open>left_nested_expr E\<close> \<open>hd (list_expr E) = a1\<close> \<open>hd (tl (list_expr E)) = a2\<close>
  shows \<open>has_subexpr (\<langle>a1\<rangle> \<star> \<langle>a2\<rangle>) E\<close>
  using assms
proof (induction E rule: left_nested_expr.induct)
  case (pair l r)
  then show ?case
    by auto
next
  case (nested L R)
  then show ?case
    by (simp; metis (mono_tags, lifting) count_expr_ge1 expr.distinct(1) expr_from_list hd_append2
        left left_nested_expr.cases list.collapse list.size(3) not_one_le_zero)
qed

text \<open>We then define a function that replaces the leftmost occurrence of a subexpression with a
different subexpression.\<close>

function replace_subexpr :: \<open>'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> 'a expr\<close> where
  \<open>\<not>has_subexpr X E \<Longrightarrow> replace_subexpr X Y E = E\<close> |
  \<open>X = E \<Longrightarrow> replace_subexpr X Y E = Y\<close> |
  \<open>\<lbrakk>X \<noteq> L \<star> R; has_subexpr X L\<rbrakk> \<Longrightarrow> replace_subexpr X Y (L \<star> R) = replace_subexpr X Y L \<star> R\<close> |
  \<open>\<lbrakk>X \<noteq> L \<star> R; \<not>has_subexpr X L; has_subexpr X R\<rbrakk> \<Longrightarrow>
    replace_subexpr X Y (L \<star> R) = L \<star> replace_subexpr X Y R\<close>
  by (auto, metis has_subexpr.cases)
termination by lexicographic_order

text \<open>Doing such a replacement removes and adds the corresponding values of the replaced and
replacement subexpressions respectively.\<close>

lemma mset_replace_subexpr:
  \<open>has_subexpr X E \<Longrightarrow> mset_expr (replace_subexpr X Y E) = mset_expr E - mset_expr X + mset_expr Y\<close>
  by (induction X Y E rule: replace_subexpr.induct; auto;
      unfold has_subexpr_simp_Op; auto simp add: mset_has_subexpr)

text \<open>If the evaluated value of the replaced and replacement subexpressions are the same, this does
not change the evaluated value of the whole expression.\<close>

lemma (in huffman_algebra) value_replace_subexpr:
  \<open>value_expr X = value_expr Y \<Longrightarrow> value_expr (replace_subexpr X Y E) = value_expr E\<close>
  by (induction X Y E rule: replace_subexpr.induct; auto)

text \<open>Any change of the subexpressions evaluated value leads to a corresponding change of the whole
expression's evaluated value.\<close>

lemma (in huffman_algebra) value_replace_subexpr_increasing:
  \<open>value_expr X \<le> value_expr Y \<Longrightarrow> value_expr E \<le> value_expr (replace_subexpr X Y E)\<close>
  by (induction X Y E rule: replace_subexpr.induct; simp add: mono;
      metis commutative mono value_expr.simps(2))

lemma (in huffman_algebra) value_replace_subexpr_decreasing:
  \<open>value_expr Y \<le> value_expr X \<Longrightarrow> value_expr (replace_subexpr X Y E) \<le> value_expr E\<close>
  by (induction X Y E rule: replace_subexpr.induct; simp add: mono;
      metis commutative mono value_expr.simps(2))

(***)

(* TODO continue here *)

lemma finite_expr_of_size:
  assumes \<open>finite U\<close>
  shows \<open>finite {E. set_expr E \<subseteq> U \<and> size E < n}\<close>
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have \<open>{E. set_expr E \<subseteq> U \<and> size E < Suc n} \<subseteq>
    (Val ` U) \<union> (\<Union>L \<in> {E. set_expr E \<subseteq> U \<and> size E < n}.
      (\<star>) L ` {E. set_expr E \<subseteq> U \<and> size E < n})\<close>
  proof
    fix E assume E: \<open>E \<in> {E. set_expr E \<subseteq> U \<and> size E < Suc n}\<close>
    hence PE: \<open>size E < Suc n\<close> \<open>set_expr E \<subseteq> U\<close>
      by auto
    show \<open>E \<in> Val ` U \<union>
      (\<Union>L\<in>{E. set_expr E \<subseteq> U \<and> size E < n}.
        (\<star>) L ` {E. set_expr E \<subseteq> U \<and> size E < n})\<close>
      by (cases E; insert PE; auto)
  qed
  then show ?case
    by (metis (no_types, lifting) Suc.IH assms finite_UN_I finite_Un finite_imageI finite_subset)
qed

lemma finite_expr_for_mset:
  \<open>finite {E. mset_expr E = A}\<close>
proof -
  have \<open>{E. mset_expr E = A} \<subseteq> {E. set_expr E \<subseteq> set_mset A \<and> size E < 2 * size A}\<close>
    by (intro Collect_mono impI; fold set_mset_expr; auto simp add: count_expr_size)
  thus ?thesis
    using finite_expr_of_size finite_subset by fastforce
qed

lemma ex_expr_for_mset:
  assumes \<open>V \<noteq> {#}\<close>
  shows \<open>\<exists>E. mset_expr E = V\<close>
proof -
  obtain v where v: \<open>v \<in># V\<close> using assms
    by blast
  obtain L where \<open>mset L = (V - {#v#})\<close>
    using ex_mset by blast
  hence Lv_mset: \<open>mset (L @ [v]) = V\<close>
    by (simp add: v)
  obtain E where E: \<open>E = foldr (\<lambda> a b. \<langle>a\<rangle> \<star> b) L \<langle>v\<rangle>\<close>
    by simp
  hence \<open>list_expr E = L @ [v]\<close>
    unfolding E by (induction L; simp)
  hence \<open>mset_expr E = V\<close>
    using Lv_mset by auto
  thus ?thesis
    by blast
qed

(***)

context huffman_algebra
begin

abbreviation value_bound_mset :: \<open>'a multiset \<Rightarrow> 'a\<close> where
  \<open>value_bound_mset A \<equiv> Min (value_expr ` {E. mset_expr E = A})\<close>

lemma value_bound_singleton:
  \<open>value_bound_mset {# a #} = a\<close>
proof - 
  have \<open>{E. mset_expr E = {# a #}} = {\<langle>a\<rangle>}\<close>
    using expr_from_mset by force
  thus ?thesis
    by simp
qed


lemma \<open>value_expr E \<ge> value_bound_mset (mset_expr E)\<close>
  by (intro Min_le; insert finite_expr_for_mset; blast)

fun huffman_step_sorted_list :: \<open>'a list \<Rightarrow> 'a multiset\<close> where
  \<open>huffman_step_sorted_list (a1 # a2 # as) = mset (a1 \<diamondop> a2 # as)\<close> |
  \<open>huffman_step_sorted_list as = mset as\<close>

abbreviation huffman_step :: \<open>'a multiset \<Rightarrow> 'a multiset\<close> where
  \<open>huffman_step A \<equiv> huffman_step_sorted_list (sorted_list_of_multiset A)\<close>

lemma huffman_step_sorted_list_size:
  \<open>length as \<ge> 2 \<Longrightarrow> Suc (size (huffman_step_sorted_list as)) = length as\<close>
  by (metis One_nat_def Suc_1 Suc_leD Suc_n_not_le_n huffman_step_sorted_list.elims length_Cons
      list.size(3) size_mset)

lemma huffman_step_size[simp]:
  \<open>size A \<ge> 2 \<Longrightarrow> size (huffman_step A) < size A\<close>
  by (metis Suc_n_not_le_n huffman_step_sorted_list_size leI mset_sorted_list_of_multiset size_mset)

lemma huffman_step_as_mset_ops:
  assumes \<open>size A \<ge> 2\<close> \<open>a1 # a2 # as = sorted_list_of_multiset A\<close>
  shows \<open>huffman_step A = A - {# a1, a2 #} + {# a1 \<diamondop> a2 #}\<close>
  by (metis add_mset_add_single add_mset_diff_bothsides add_mset_remove_trivial assms(2)
      huffman_step_sorted_list.simps(1) mset.simps(2) mset_sorted_list_of_multiset)

lemma Min_image_corr_le:
  assumes \<open>finite A\<close> \<open>A \<noteq> {}\<close> \<open>finite B\<close> \<open>\<And>a. a \<in> A \<Longrightarrow> \<exists>b \<in> B. f b \<le> f a\<close>
  shows \<open>Min (f ` B) \<le> Min (f ` A)\<close>
proof -
  have \<open>\<And>a. a \<in> A \<Longrightarrow> Min (f ` B) \<le> f a\<close>
    by (meson Min_le assms(3) assms(4) finite_imageI imageI le_less_trans not_le)
  thus ?thesis
    by (simp add: assms(1) assms(2))
qed

lemma value_bound_via_correspondence:
  assumes \<open>V1 \<noteq> {#}\<close>
    \<open>\<And>E1. mset_expr E1 = V1 \<Longrightarrow> \<exists>E2. mset_expr E2 = V2 \<and> value_expr E2 \<le> value_expr E1\<close>
  shows \<open>value_bound_mset V2 \<le> value_bound_mset V1\<close>
  by (intro Min_image_corr_le; auto simp add: assms finite_expr_for_mset ex_expr_for_mset)

lemma combine_step_lower_bound:
  assumes \<open>{# a1, a2 #} \<subseteq># A\<close>
  shows \<open>value_bound_mset A \<le> value_bound_mset (A - {# a1, a2 #} + {# a1 \<diamondop> a2 #})\<close>
proof (intro value_bound_via_correspondence; (simp; fail)?)
  fix E1 assume E1: \<open>mset_expr E1 = A - {#a1, a2#} + {#a1 \<diamondop> a2#}\<close>
  hence \<open>has_subexpr \<langle>a1 \<diamondop> a2\<rangle> E1\<close>
    by (metis add_mset_add_single has_subexpr_Val set_mset_expr union_single_eq_member)
  hence \<open>mset_expr (replace_subexpr \<langle>a1 \<diamondop> a2\<rangle> (\<langle>a1\<rangle> \<star> \<langle>a2\<rangle>) E1) = A\<close>
    by (simp add: mset_replace_subexpr; insert E1 assms subset_mset.diff_add; fastforce)
  moreover have \<open>value_expr (replace_subexpr \<langle>a1 \<diamondop> a2\<rangle> (\<langle>a1\<rangle> \<star> \<langle>a2\<rangle>) E1) = value_expr E1\<close>
      by (simp add: value_replace_subexpr)
  ultimately show \<open>\<exists>E2. mset_expr E2 = A \<and> value_expr E2 \<le> value_expr E1\<close>
    by auto
qed

lemma (in huffman_algebra) huffman_step_lower_bound:
  assumes \<open>A \<noteq> {#}\<close>
  shows \<open>value_bound_mset A \<le> value_bound_mset (huffman_step A)\<close>
proof (cases \<open>size A < 2\<close>)
  case True
  then obtain a where \<open>A = {# a #}\<close>
    using assms less_2_cases size_1_singleton_mset by auto
  then show ?thesis
    by auto
next
  case False
  then obtain a1 a2 as where V: \<open>a1 # a2 # as = sorted_list_of_multiset A\<close>
    by (metis One_nat_def Suc_1 assms length_Cons lessI list.size(3) mset.simps(1)
        mset_sorted_list_of_multiset remdups_adj.cases size_mset)
  hence a1a2_in_A: \<open>{# a1, a2 #} \<subseteq># A\<close>
    by (metis empty_le mset.simps(2) mset_sorted_list_of_multiset mset_subset_eq_add_mset_cancel)
    
  show ?thesis
    using huffman_step_as_mset_ops[of A a1 a2 as]  False V a1a2_in_A
      combine_step_lower_bound huffman_algebra_axioms by auto
qed

lemma huffman_step_upper_bound:
  assumes \<open>A \<noteq> {#}\<close>
  shows \<open>value_bound_mset (huffman_step A) \<le> value_bound_mset A\<close>
proof (intro value_bound_via_correspondence)
  show \<open>A \<noteq> {#}\<close>
    by (simp add: assms)
next
  fix E1 assume E1: \<open>mset_expr E1 = A\<close>
  show \<open>\<exists>E2. mset_expr E2 = huffman_step A \<and> value_expr E2 \<le> value_expr E1\<close>
  proof (cases \<open>size A < 2\<close>)
    case True
    then obtain a where A: \<open>A = {#a#}\<close>
      using assms less_2_cases size_1_singleton_mset by auto
    then show ?thesis
      using E1 by auto
  next
    case False
    then obtain a1 a2 as where V: \<open>a1 # a2 # as = sorted_list_of_multiset A\<close>
      by (metis Suc_le_length_iff leI mset_sorted_list_of_multiset numeral_2_eq_2 size_mset)
    obtain H where H: \<open>H = rearrange_expr E1\<close> 
      by simp

    have H_is_Op: \<open>is_Op H\<close>
      by (metis E1 False H is_Op_by_count leI rearrange_expr_mset size_mset)
    have H_bound: \<open>value_expr H \<le> value_expr E1\<close>
      by (simp add: H value_rearrange_expr)

    have \<open>left_nested_expr H\<close>
      by (metis E1 False H is_Op_by_count le_less_linear left_nested_rearrange_expr size_mset)
    moreover have \<open>hd (list_expr H) = a1\<close>
      by (metis H E1 V hd_list_rearrange_expr list.sel(1))
    moreover have \<open>hd (tl (list_expr H)) = a2\<close>
      by (metis E1 H V hd_tl_list_rearrange_expr list.sel(1) list.sel(3))
    ultimately have H_subexpr: \<open>has_subexpr (\<langle>a1\<rangle> \<star> \<langle>a2\<rangle>) H\<close>
      by (simp add: left_nested_expr_has_hd2_subexpr)

    then obtain E2 where E2: \<open>E2 = replace_subexpr (\<langle>a1\<rangle> \<star> \<langle>a2\<rangle>) \<langle>a1 \<diamondop> a2\<rangle> H\<close>
      by simp
    hence \<open>value_expr E2 \<le> value_expr E1\<close>
      by (simp add: H_bound value_replace_subexpr)

    moreover have \<open>mset_expr E2 = A - {# a1, a2 #} + {# a1 \<diamondop> a2 #}\<close>
      by (metis (mono_tags, lifting) E1 E2 H H_subexpr append.simps(2) append_self_conv2
          expr.simps(7) expr.simps(8) mset.simps(1) mset.simps(2) mset_replace_subexpr
          rearrange_expr_mset)
    hence \<open>mset_expr E2 = huffman_step A\<close>
      using False V huffman_step_as_mset_ops by auto

    ultimately show ?thesis
      by blast
  qed
qed

lemma value_huffman_step:
  \<open>value_bound_mset (huffman_step A) = value_bound_mset A\<close>
  by (cases \<open>A = {#}\<close>; insert huffman_step_lower_bound huffman_step_upper_bound; force)

function value_bound_huffman :: \<open>'a multiset \<Rightarrow> 'a\<close> where
  \<open>value_bound_huffman A = (case size A of
    0 \<Rightarrow> Min {} |
    Suc 0 \<Rightarrow> the_elem (set_mset A) |
    Suc (Suc _) \<Rightarrow> value_bound_huffman (huffman_step A)
  )\<close> 
  by pat_completeness auto
termination
  by (relation \<open>measure size\<close>; simp;
      metis Suc_1 Suc_le_eq less_add_Suc1 local.huffman_step_size plus_1_eq_Suc)

lemma value_bound_huffman_singleton:
  \<open>value_bound_mset {#a#} = value_bound_huffman {#a#}\<close>
  by (subst value_bound_singleton; simp)

lemma value_bound_huffman_nonsingleton:
  \<open>size A = Suc n \<Longrightarrow> value_bound_mset A = value_bound_huffman A\<close>
proof (induction n arbitrary: A)
  case 0
  then obtain a where \<open>A = {# a #}\<close>
    by (metis One_nat_def size_1_singleton_mset)
  then show ?case
    using value_bound_huffman_singleton by blast
next
  case (Suc n)
  have \<open>size (huffman_step A) = Suc n\<close>
    by (metis Suc.prems Suc_1 Suc_le_eq add_diff_cancel_left' less_add_Suc1
        local.huffman_step_sorted_list_size mset_sorted_list_of_multiset plus_1_eq_Suc size_mset)
  hence \<open>value_bound_huffman (huffman_step A) = value_bound_mset (huffman_step A)\<close>
    using Suc.IH by auto
  then show ?case
    by (subst value_bound_huffman.simps; simp add: Suc.prems value_huffman_step)
qed

lemma value_bound_huffman_mset:
  \<open>value_bound_mset A = value_bound_huffman A\<close>
  by (cases \<open>size A\<close>; insert value_bound_huffman_nonsingleton; auto)

(***)

lemma value_expr_homo:
  assumes \<open>\<And>a b. f (a \<diamondop> b) = f a \<diamondop> f b\<close>
  shows \<open>value_expr (map_expr f E) = f (value_expr E)\<close>
  using assms
  by (induction E; auto)

lemma value_expr_mono:
  assumes \<open>\<And>a b. f (a \<diamondop> b) \<le> f a \<diamondop> f b\<close> 
  shows \<open>f (value_expr E) \<le> value_expr (map_expr f E)\<close>
  using assms
proof (induction E; (simp; fail)?)
  case (Op L R)

  have L: \<open>f (value_expr L) \<le> value_expr (map_expr f L)\<close>
    and R: \<open>f (value_expr R) \<le> value_expr (map_expr f R)\<close>
    using Op.IH assms by auto 
  hence \<open>f (value_expr L) \<diamondop> f (value_expr R) \<le> f (value_expr L) \<diamondop> value_expr (map_expr f R)\<close>
    using local.commutative local.mono by fastforce
  hence \<open>f (value_expr L) \<diamondop> f (value_expr R) \<le> value_expr (map_expr f L) \<diamondop> value_expr (map_expr f R)\<close>
    by (metis L local.mono min.absorb2 min.coboundedI1)
  hence \<open>f (value_expr L \<diamondop> value_expr R) \<le> value_expr (map_expr f L) \<diamondop> value_expr (map_expr f R)\<close>
    using assms dual_order.trans by blast
  then show ?case
    by simp
qed

lemma mset_expr_map_expr:
  \<open>list_expr (map_expr f E) = map f (list_expr E)\<close>
  by (induction E; auto)

lemma unmap_list_expr:
  \<open>list_expr E = map f as \<Longrightarrow> \<exists>E'. E = map_expr f E' \<and> list_expr E' = as\<close>
proof (induction E arbitrary: as)
  case (Val b)
  then obtain a where \<open>as = [a]\<close>
    by auto
  then show ?case
    by (metis Val.prems expr.simps(7) expr.simps(9) list.sel(1) list.simps(9))
next
  case (Op L R)
  obtain ls where ls: \<open>ls = take (length (list_expr L)) as\<close>
    by blast
  obtain rs where rs: \<open>rs = drop (length (list_expr L)) as\<close>
    by blast
  have \<open>list_expr L = map f ls\<close>
    by (metis (mono_tags, lifting) Op.prems append_eq_conv_conj expr.simps(8) ls take_map)
  then obtain L' where L': \<open>L = map_expr f L' \<and> list_expr L' = ls\<close>
    using Op.IH(1) by blast

  have \<open>list_expr R = map f rs\<close>
    by (metis (mono_tags, lifting) Op.prems append_eq_conv_conj drop_map expr.simps(8) rs)
  then obtain R' where R': \<open>R = map_expr f R' \<and> list_expr R' = rs\<close>
    using Op.IH(2) by blast

  have \<open>L \<star> R = map_expr f (L' \<star> R') \<and> list_expr (L' \<star> R') = as\<close>
    by (simp add: L' R' ls rs)
  thus ?case
    by blast
qed

lemma unmap_image_mset:
  \<open>mset as = image_mset f B \<Longrightarrow> \<exists>bs. as = map f bs \<and> B = mset bs\<close>
proof (induction as arbitrary: B)
  case Nil
  then show ?case
    by simp
next
  case (Cons a as)
  obtain B' b where *: \<open>mset as = image_mset f B' \<and> a = f b \<and> B = add_mset b B'\<close>
    by (metis Cons.prems msed_map_invR mset.simps(2))
  then obtain bs where **: \<open>as = map f bs \<and> B' = mset bs\<close>
    using Cons.IH by blast

  have \<open>a # as = map f (b # bs) \<and> B = mset (b # bs)\<close>
    by (simp add: * **)
  then show ?case
    by metis
qed

lemma unmap_mset_expr:
  assumes \<open>mset_expr E = image_mset f A\<close>
  shows \<open>\<exists>E'. E = map_expr f E' \<and> mset_expr E' = A\<close>
proof -
  obtain es where es: \<open>es = list_expr E\<close>
    by simp
  then obtain as where \<open>es = map f as \<and> A = mset as\<close>
    using unmap_image_mset[of es f A] assms
    by blast
  thus ?thesis
    using es unmap_list_expr by fastforce
qed

lemma map_expr_inv: \<open>set_expr E \<subseteq> range f \<Longrightarrow> map_expr f (map_expr (inv f) E) = E\<close>
  by (induction E; simp add: f_inv_into_f)

lemma value_expr_map_expr_inv_homo:
  assumes \<open>\<And>a b. f (a \<diamondop> b) = f a \<diamondop> f b\<close> \<open>set_expr E \<subseteq> range f\<close>
  shows \<open>f (value_expr (map_expr (inv f) E)) = value_expr E\<close>
  using assms
  by (induction E; simp add: f_inv_into_f)

lemma map_expr_inv_homo_image_mset:
  assumes \<open>\<And>a b. f (a \<diamondop> b) = f a \<diamondop> f b\<close> \<open>mset_expr E = image_mset f A\<close>
  shows \<open>(map_expr f (map_expr (inv f) E) = E) \<and> (f (value_expr (map_expr (inv f) E)) = value_expr E)\<close>
proof -
  have \<open>set_expr E \<subseteq> range f\<close>
    unfolding set_mset_expr[symmetric]
    using assms by auto
  thus ?thesis
    by (simp add: assms(1) map_expr_inv value_expr_map_expr_inv_homo)
qed

lemma map_exprs_for_mset:
  \<open>{E. mset_expr E = image_mset f A} = map_expr f ` {E. mset_expr E = A}\<close>
proof (rule; rule)
  fix x assume \<open>x \<in> {E. mset_expr E = image_mset f A}\<close>
  thus \<open>x \<in> map_expr f ` {E. mset_expr E = A}\<close>
    using unmap_mset_expr by fastforce
next
  fix x assume \<open>x \<in> map_expr f ` {E. mset_expr E = A}\<close>
  thus \<open>x \<in> {E. mset_expr E = image_mset f A}\<close>
    by (metis (mono_tags, lifting) imageE mem_Collect_eq mset_expr_map_expr mset_map)
qed

lemma value_bound_homo:
  assumes \<open>\<And>a b. f (a \<diamondop> b) = f a \<diamondop> f b\<close> \<open>mono f\<close> \<open>A \<noteq> {#}\<close>
  shows \<open>value_bound_mset (image_mset f A) = f (value_bound_mset A)\<close>
proof -
  have \<open>value_expr ` {E. mset_expr E = image_mset f A} =
      (value_expr \<circ> map_expr f) ` {E. mset_expr E = A}\<close>
    by (simp add: image_comp map_exprs_for_mset)
  moreover have \<open>(f \<circ> value_expr) ` {E. mset_expr E = A} =
      (value_expr \<circ> map_expr f) ` {E. mset_expr E = A}\<close>
    using assms(1) value_expr_homo by auto
  ultimately have \<open>value_expr ` {E. mset_expr E = image_mset f A} =
      f ` value_expr ` {E. mset_expr E = A}\<close>
    by (simp add: image_comp)
  hence \<open>value_bound_mset (image_mset f A) = Min (f ` value_expr ` {E. mset_expr E = A})\<close>
    by simp
  moreover have \<open>finite (value_expr ` {E. mset_expr E = A})\<close>
    using finite_expr_for_mset by blast
  ultimately show ?thesis
    using mono_Min_commute[of f \<open>value_expr ` {E. mset_expr E = A}\<close>]
    by (simp add: assms ex_expr_for_mset)
qed

lemma Min_corr_image_le:
  assumes \<open>finite A\<close> \<open>A \<noteq> {}\<close> \<open>\<And>a. a \<in> A \<Longrightarrow> f a \<le> g a\<close>
  shows \<open>Min (f ` A) \<le> Min (g ` A)\<close>
proof -
  have \<open>\<And>a. a \<in> A \<Longrightarrow> Min (f ` A) \<le> g a\<close>
    using Min_le_iff assms(1) assms(3) by auto
  thus ?thesis
    by (simp add: assms(1) assms(2))
qed

lemma value_bound_mono:
  assumes \<open>\<And>a b. f (a \<diamondop> b) \<le> f a \<diamondop> f b\<close> \<open>mono f\<close> \<open>A \<noteq> {#}\<close>
  shows \<open>f (value_bound_mset A) \<le> value_bound_mset (image_mset f A)\<close>
proof -
  have \<open>value_expr ` {E. mset_expr E = image_mset f A} =
      (value_expr \<circ> map_expr f) ` {E. mset_expr E = A}\<close>
    by (simp add: image_comp map_exprs_for_mset)
  moreover have \<open>Min ((f \<circ> value_expr) ` {E. mset_expr E = A}) \<le>
      Min ((value_expr \<circ> map_expr f) ` {E. mset_expr E = A})\<close>
    by (intro Min_corr_image_le;
        simp add: assms finite_expr_for_mset ex_expr_for_mset value_expr_mono)
  ultimately show ?thesis
    by (simp add: assms ex_expr_for_mset finite_expr_for_mset image_comp mono_Min_commute)
qed

lemma value_bound_increasing:
  assumes \<open>a \<in># A\<close> \<open>b \<ge> a\<close>
  shows \<open>value_bound_mset A \<le> value_bound_mset (A - {# a #} + {# b #})\<close>
proof (intro value_bound_via_correspondence; (simp; fail)?)
  fix E1 assume E1: \<open>mset_expr E1 = A - {#a#} + {#b#}\<close>

  hence \<open>has_subexpr \<langle>b\<rangle> E1\<close>
    by (metis add_mset_add_single has_subexpr_Val set_mset_expr union_single_eq_member)

  hence \<open>mset_expr (replace_subexpr \<langle>b\<rangle> \<langle>a\<rangle> E1) = A\<close>
    by (simp add: E1 assms(1) mset_replace_subexpr)

  moreover have \<open>value_expr (replace_subexpr \<langle>b\<rangle> \<langle>a\<rangle> E1) \<le> value_expr E1\<close>
    by (simp add: assms(2) value_replace_subexpr_decreasing)

  ultimately show \<open>\<exists>E2. mset_expr E2 = A \<and> value_expr E2 \<le> value_expr E1\<close>
    by blast
qed

end

end
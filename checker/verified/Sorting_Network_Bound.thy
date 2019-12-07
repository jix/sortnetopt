theory Sorting_Network_Bound
  imports Main
begin

text \<open>Due to the 0-1-principle we're only concerned with Boolean vectors. While we're interested in
sorting vectors of a given fixed width, it is advantageous to represent them as a function from the
naturals to Boolens.\<close>

type_synonym vect = \<open>nat \<Rightarrow> bool\<close>

text \<open>To represent vectors of a fixed width, we extend them with True to infinity. This way
monotonicity of a fixed width vector corresponds to monotonicity of our representation.\<close>

definition fixed_width_vect :: \<open>nat \<Rightarrow> vect \<Rightarrow> bool\<close> where
  \<open>fixed_width_vect n v = (\<forall>i \<ge> n. v i = True)\<close>

text \<open>A comparator is represented as an ordered pair of channel indices. Applying a comparator to a
vector will order the values of the two channels so that the channel corresponding to the first
index receives the smaller value.\<close>

type_synonym cmp = \<open>nat \<times> nat\<close>

definition apply_cmp :: \<open>cmp \<Rightarrow> vect \<Rightarrow> vect\<close> where
  \<open>apply_cmp c v = (
    let (a, b) = c
    in v(
      a := min (v a) (v b),
      b := max (v a) (v b)
    )
  )\<close>

text \<open>A lower size bound for a sorting network on a given set of input vectors is a number of
comparators so that any network that is able to sort every vector of the input set has at least that
number of comparators.\<close>

definition lower_size_bound :: \<open>vect set \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>lower_size_bound V b = (\<forall>cn. (\<forall>v \<in> V. mono (fold apply_cmp cn v)) \<longrightarrow> length cn \<ge> b)\<close>

text \<open>We are interested in lower size bounds for sorting networks that sort all vectors of a given
  width.\<close>

definition lower_size_bound_for_width :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>lower_size_bound_for_width w b = lower_size_bound {v. fixed_width_vect w v} b\<close>

end
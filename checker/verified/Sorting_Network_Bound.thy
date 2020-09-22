theory Sorting_Network_Bound
  imports Main
begin

text \<open>Due to the 0-1-principle we're only concerned with Boolean sequences. While we're interested
in sorting vectors of a given fixed width, it is advantageous to represent them as a function from
the naturals to Booleans.\<close>

type_synonym bseq = \<open>nat \<Rightarrow> bool\<close>

text \<open>To represent Boolean sequences of a fixed length, we extend them with True to infinity. This
way monotonicity of a fixed length sequence corresponds to monotonicity of our representation.\<close>

definition fixed_len_bseq :: \<open>nat \<Rightarrow> bseq \<Rightarrow> bool\<close> where
  \<open>fixed_len_bseq n x = (\<forall>i \<ge> n. x i = True)\<close>

text \<open>A comparator is represented as an ordered pair of channel indices. Applying a comparator to a
sequence will order the values of the two channels so that the channel corresponding to the first
index receives the smaller value.\<close>

type_synonym cmp = \<open>nat \<times> nat\<close>

definition apply_cmp :: \<open>cmp \<Rightarrow> bseq \<Rightarrow> bseq\<close> where
  \<open>apply_cmp c x = (
    let (i, j) = c
    in x(
      i := min (x i) (x j),
      j := max (x i) (x j)
    )
  )\<close>

text \<open>A lower size bound for a partial sorting network on a given set of input sequences is the
number of comparators required for any comparator network that is able to sort every sequence of the
given set.\<close>

definition partial_lower_size_bound :: \<open>bseq set \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>partial_lower_size_bound X k = (\<forall>cn. (\<forall>x \<in> X. mono (fold apply_cmp cn x)) \<longrightarrow> length cn \<ge> k)\<close>

text \<open>A lower size bound for a sorting network on n channels is the same as a lower size bound for a
partial sorting network on all length n sequences.\<close>

definition lower_size_bound :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>lower_size_bound n k = partial_lower_size_bound {x. fixed_len_bseq n x} k\<close>

end
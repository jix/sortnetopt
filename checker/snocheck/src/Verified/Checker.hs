-- Generated using update_extracted_code.sh, do not edit --
{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Verified.Checker(Int(..), Proof_witness(..), Proof_step_witnesses(..),
                    Proof_step(..), Proof_cert(..), integer_of_int,
                    check_proof_get_bound)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified Parallel;

newtype Nat = Nat Integer;

integer_of_nat :: Nat -> Integer;
integer_of_nat (Nat x) = x;

equal_nat :: Nat -> Nat -> Bool;
equal_nat m n = integer_of_nat m == integer_of_nat n;

instance Eq Nat where {
  a == b = equal_nat a b;
};

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat m n = integer_of_nat m <= integer_of_nat n;

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

less_nat :: Nat -> Nat -> Bool;
less_nat m n = integer_of_nat m < integer_of_nat n;

instance Ord Nat where {
  less_eq = less_eq_nat;
  less = less_nat;
};

class (Ord a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

instance Preorder Nat where {
};

instance Order Nat where {
};

class (Order a) => Linorder a where {
};

instance Linorder Nat where {
};

instance Ord Integer where {
  less_eq = (\ a b -> a <= b);
  less = (\ a b -> a < b);
};

newtype Int = Int_of_integer Integer;

data Num = One | Bit0 Num | Bit1 Num;

data Set a = Set [a] | Coset [a];

data Vect_trie = VtEmpty | VtNode !Bool !Vect_trie !Vect_trie;

newtype Multiset a = Mset [a];

data Proof_witness = ProofWitness Int Bool [Int];

data Proof_step_witnesses = HuffmanWitnesses Bool [Maybe Proof_witness]
  | SuccessorWitnesses [Maybe Proof_witness];

data Proof_step = ProofStep Int [[Bool]] Int Proof_step_witnesses;

data Proof_cert = ProofCert Int (Int -> Proof_step);

integer_of_int :: Int -> Integer;
integer_of_int (Int_of_integer k) = k;

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

nat :: Int -> Nat;
nat k = Nat (max (0 :: Integer) (integer_of_int k));

plus_nat :: Nat -> Nat -> Nat;
plus_nat m n = Nat (integer_of_nat m + integer_of_nat n);

one_nat :: Nat;
one_nat = Nat (1 :: Integer);

suc :: Nat -> Nat;
suc n = plus_nat n one_nat;

minus_nat :: Nat -> Nat -> Nat;
minus_nat m n = Nat (max (0 :: Integer) (integer_of_nat m - integer_of_nat n));

zero_nat :: Nat;
zero_nat = Nat (0 :: Integer);

nth :: forall a. [a] -> Nat -> a;
nth (x : xs) n =
  (if equal_nat n zero_nat then x else nth xs (minus_nat n one_nat));

upt :: Nat -> Nat -> [Nat];
upt i j = (if less_nat i j then i : upt (suc i) j else []);

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f (x : xs) s = fold f xs (f x s);
fold f [] s = s;

par :: forall a b. a -> b -> b;
par = Parallel.par;

member :: forall a. (Eq a) => [a] -> a -> Bool;
member [] y = False;
member (x : xs) y = x == y || member xs y;

pred :: Nat -> Nat;
pred = nat_pred_code;

nat_pred_code :: Nat -> Nat;
nat_pred_code n =
  (if equal_nat n zero_nat then pred zero_nat else minus_nat n one_nat);

the_elem :: forall a. Set a -> a;
the_elem (Set [x]) = x;

distinct :: forall a. (Eq a) => [a] -> Bool;
distinct [] = True;
distinct (x : xs) = not (member xs x) && distinct xs;

is_none :: forall a. Maybe a -> Bool;
is_none (Just x) = False;
is_none Nothing = True;

list_vt_extend :: Vect_trie -> ([Bool] -> [Bool]) -> [[Bool]] -> [[Bool]];
list_vt_extend VtEmpty el_prefix suffix = suffix;
list_vt_extend (VtNode True lo hi) el_prefix suffix =
  el_prefix [] :
    list_vt_extend lo (el_prefix . (\ a -> False : a))
      (list_vt_extend hi (el_prefix . (\ a -> True : a)) suffix);
list_vt_extend (VtNode False lo hi) el_prefix suffix =
  list_vt_extend lo (el_prefix . (\ a -> False : a))
    (list_vt_extend hi (el_prefix . (\ a -> True : a)) suffix);

list_vt :: Vect_trie -> [[Bool]];
list_vt a = list_vt_extend a id [];

vt_singleton :: [Bool] -> Vect_trie;
vt_singleton [] = VtNode True VtEmpty VtEmpty;
vt_singleton (False : xs) = VtNode False (vt_singleton xs) VtEmpty;
vt_singleton (True : xs) = VtNode False VtEmpty (vt_singleton xs);

vt_union :: Vect_trie -> Vect_trie -> Vect_trie;
vt_union VtEmpty VtEmpty = VtEmpty;
vt_union (VtNode v va vb) VtEmpty = VtNode v va vb;
vt_union VtEmpty (VtNode v va vb) = VtNode v va vb;
vt_union (VtNode a a_lo a_hi) (VtNode b b_lo b_hi) =
  VtNode (a || b) (vt_union a_lo b_lo) (vt_union a_hi b_hi);

vt_list :: [[Bool]] -> Vect_trie;
vt_list ls = fold (vt_union . vt_singleton) ls VtEmpty;

gen_length :: forall a. Nat -> [a] -> Nat;
gen_length n (x : xs) = gen_length (suc n) xs;
gen_length n [] = n;

list_update :: forall a. [a] -> Nat -> a -> [a];
list_update [] i y = [];
list_update (x : xs) i y =
  (if equal_nat i zero_nat then y : xs
    else x : list_update xs (minus_nat i one_nat) y);

witness_step_id :: Proof_witness -> Int;
witness_step_id (ProofWitness x1 x2 x3) = x1;

witness_invert :: Proof_witness -> Bool;
witness_invert (ProofWitness x1 x2 x3) = x2;

witness_perm :: Proof_witness -> [Int];
witness_perm (ProofWitness x1 x2 x3) = x3;

step_vect_list :: Proof_step -> [[Bool]];
step_vect_list (ProofStep x1 x2 x3 x4) = x2;

size_list :: forall a. [a] -> Nat;
size_list = gen_length zero_nat;

step_bound :: Proof_step -> Int;
step_bound (ProofStep x1 x2 x3 x4) = x3;

less_eq_int :: Int -> Int -> Bool;
less_eq_int k l = integer_of_int k <= integer_of_int l;

zero_int :: Int;
zero_int = Int_of_integer (0 :: Integer);

less_int :: Int -> Int -> Bool;
less_int k l = integer_of_int k < integer_of_int l;

length_vt :: Vect_trie -> Nat;
length_vt VtEmpty = zero_nat;
length_vt (VtNode True lo hi) = suc (plus_nat (length_vt lo) (length_vt hi));
length_vt (VtNode False lo hi) = plus_nat (length_vt lo) (length_vt hi);

is_unsorted_vt :: Nat -> Vect_trie -> Bool;
is_unsorted_vt n a = less_nat (suc n) (length_vt a);

is_subset_vt :: Vect_trie -> Vect_trie -> Bool;
is_subset_vt VtEmpty a = True;
is_subset_vt (VtNode True a_lo a_hi) VtEmpty = False;
is_subset_vt (VtNode False a_lo a_hi) VtEmpty =
  is_subset_vt a_lo VtEmpty && is_subset_vt a_hi VtEmpty;
is_subset_vt (VtNode True a_lo a_hi) (VtNode False b_lo b_hi) = False;
is_subset_vt (VtNode False a_lo a_hi) (VtNode b b_lo b_hi) =
  is_subset_vt a_lo b_lo && is_subset_vt a_hi b_hi;
is_subset_vt (VtNode True a_lo a_hi) (VtNode True b_lo b_hi) =
  is_subset_vt a_lo b_lo && is_subset_vt a_hi b_hi;

permute_list_vect :: [Nat] -> [Bool] -> [Bool];
permute_list_vect ps xs = map (nth xs) ps;

permute_vt :: [Nat] -> Vect_trie -> Vect_trie;
permute_vt ps a = vt_list (map (permute_list_vect ps) (list_vt a));

invert_vt :: Bool -> Vect_trie -> Vect_trie;
invert_vt z a = (if z then vt_list (map (map not) (list_vt a)) else a);

get_bound ::
  (Int -> Proof_step) ->
    Int -> Maybe Proof_witness -> Nat -> Vect_trie -> Maybe Nat;
get_bound proof_steps step_limit Nothing width a =
  Just (if is_unsorted_vt width a then one_nat else zero_nat);
get_bound proof_steps step_limit (Just witness) width a =
  let {
    witness_id = witness_step_id witness;
    perm = map nat (witness_perm witness);
    step = proof_steps witness_id;
    b_list = step_vect_list step;
    b = vt_list b_list;
    ba = permute_vt perm (invert_vt (witness_invert witness) b);
  } in (if not (less_eq_int zero_int witness_id &&
                 less_int witness_id step_limit) ||
             (not (all (\ i -> less_eq_nat zero_nat i && less_nat i width)
                    perm) ||
               (not (equal_nat (size_list perm) width) ||
                 (not (distinct perm) ||
                   (not (all (\ xs -> equal_nat (size_list xs) width) b_list) ||
                     not (is_subset_vt ba a)))))
         then Nothing else Just (nat (step_bound step)));

ocmp_list :: Nat -> [(Nat, Nat)];
ocmp_list n =
  concatMap (\ i -> map (\ j -> (j, i)) (upt zero_nat i)) (upt zero_nat n);

set_mset :: forall a. Multiset a -> Set a;
set_mset (Mset xs) = Set xs;

the :: forall a. Maybe a -> a;
the (Just x2) = x2;

step_witnesses :: Proof_step -> Proof_step_witnesses;
step_witnesses (ProofStep x1 x2 x3 x4) = x4;

step_width :: Proof_step -> Int;
step_width (ProofStep x1 x2 x3 x4) = x1;

is_redundant_cmp_vt :: (Nat, Nat) -> Vect_trie -> Bool;
is_redundant_cmp_vt (aa, b) a =
  let {
    vs = list_vt a;
  } in not (not (all (\ x -> not (nth x aa && not (nth x b))) vs) &&
             not (all (\ x -> not (not (nth x aa) && nth x b)) vs));

apply_cmp_list :: (Nat, Nat) -> [Bool] -> [Bool];
apply_cmp_list (a, b) xs =
  let {
    xa = nth xs a;
    xb = nth xs b;
  } in list_update (list_update xs a (xa && xb)) b (xa || xb);

list_all2 :: forall a b. (a -> b -> Bool) -> [a] -> [b] -> Bool;
list_all2 p (x : xs) (y : ys) = p x y && list_all2 p xs ys;
list_all2 p xs [] = null xs;
list_all2 p [] ys = null ys;

check_successors :: (Int -> Proof_step) -> Int -> Proof_step -> Bool;
check_successors proof_steps step_limit step =
  (case step_witnesses step of {
    HuffmanWitnesses _ _ -> False;
    SuccessorWitnesses witnesses ->
      let {
        width = nat (step_width step);
        bound = nat (step_bound step);
        ocmps = ocmp_list width;
        a_list = step_vect_list step;
        a = vt_list a_list;
        nrcmps = filter (\ c -> not (is_redundant_cmp_vt c a)) ocmps;
        bs = map (\ c -> vt_list (map (apply_cmp_list c) a_list)) nrcmps;
      } in not (equal_nat bound zero_nat) &&
             is_unsorted_vt width a &&
               equal_nat (size_list nrcmps) (size_list witnesses) &&
                 all (\ xs -> equal_nat (size_list xs) width) a_list &&
                   list_all2
                     (\ b w ->
                       (case get_bound proof_steps step_limit w width b of {
                         Nothing -> False;
                         Just ba -> less_eq_nat bound (suc ba);
                       }))
                     bs witnesses;
  });

sucmax :: Nat -> Nat -> Nat;
sucmax a b = suc (max a b);

sucmax_huffman_step_sorted_list :: [Nat] -> Multiset Nat;
sucmax_huffman_step_sorted_list (a1 : a2 : asa) = Mset (sucmax a1 a2 : asa);
sucmax_huffman_step_sorted_list [] = Mset [];
sucmax_huffman_step_sorted_list [v] = Mset [v];

apsnd :: forall a b c. (a -> b) -> (c, a) -> (c, b);
apsnd f (x, y) = (x, f y);

divmod_integer :: Integer -> Integer -> (Integer, Integer);
divmod_integer k l =
  (if k == (0 :: Integer) then ((0 :: Integer), (0 :: Integer))
    else (if (0 :: Integer) < l
           then (if (0 :: Integer) < k then divMod (abs k) (abs l)
                  else (case divMod (abs k) (abs l) of {
                         (r, s) ->
                           (if s == (0 :: Integer)
                             then (negate r, (0 :: Integer))
                             else (negate r - (1 :: Integer), l - s));
                       }))
           else (if l == (0 :: Integer) then ((0 :: Integer), k)
                  else apsnd negate
                         (if k < (0 :: Integer) then divMod (abs k) (abs l)
                           else (case divMod (abs k) (abs l) of {
                                  (r, s) ->
                                    (if s == (0 :: Integer)
                                      then (negate r, (0 :: Integer))
                                      else (negate r - (1 :: Integer),
     negate l - s));
                                })))));

divide_integer :: Integer -> Integer -> Integer;
divide_integer k l = fst (divmod_integer k l);

divide_nat :: Nat -> Nat -> Nat;
divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

part :: forall a b. (Linorder b) => (a -> b) -> b -> [a] -> ([a], ([a], [a]));
part f pivot (x : xs) =
  (case part f pivot xs of {
    (lts, (eqs, gts)) ->
      let {
        xa = f x;
      } in (if less xa pivot then (x : lts, (eqs, gts))
             else (if less pivot xa then (lts, (eqs, x : gts))
                    else (lts, (x : eqs, gts))));
  });
part f pivot [] = ([], ([], []));

nat_of_integer :: Integer -> Nat;
nat_of_integer k = Nat (max (0 :: Integer) k);

sort_key :: forall a b. (Linorder b) => (a -> b) -> [a] -> [a];
sort_key f xs =
  (case xs of {
    [] -> [];
    [_] -> xs;
    [x, y] -> (if less_eq (f x) (f y) then xs else [y, x]);
    _ : _ : _ : _ ->
      (case part f
              (f (nth xs
                   (divide_nat (size_list xs) (nat_of_integer (2 :: Integer)))))
              xs
        of {
        (lts, (eqs, gts)) -> sort_key f lts ++ eqs ++ sort_key f gts;
      });
  });

sorted_list_of_multiset :: forall a. (Linorder a) => Multiset a -> [a];
sorted_list_of_multiset (Mset xs) = sort_key (\ x -> x) xs;

size_multiset :: forall a. Multiset a -> Nat;
size_multiset (Mset xs) = size_list xs;

min :: forall a. (Ord a) => a -> a -> a;
min a b = (if less_eq a b then a else b);

mina :: forall a. (Linorder a) => Set a -> a;
mina (Set (x : xs)) = fold min xs x;

bot_set :: forall a. Set a;
bot_set = Set [];

sucmax_value_bound_huffman :: Multiset Nat -> Nat;
sucmax_value_bound_huffman a =
  (if equal_nat (size_multiset a) zero_nat then mina bot_set
    else (if equal_nat (minus_nat (size_multiset a) one_nat) zero_nat
           then the_elem (set_mset a)
           else sucmax_value_bound_huffman
                  (sucmax_huffman_step_sorted_list
                    (sorted_list_of_multiset a))));

is_member_vt :: [Bool] -> Vect_trie -> Bool;
is_member_vt uu VtEmpty = False;
is_member_vt [] (VtNode a uv uw) = a;
is_member_vt (False : xs) (VtNode ux a_lo uy) = is_member_vt xs a_lo;
is_member_vt (True : xs) (VtNode uz va a_hi) = is_member_vt xs a_hi;

extremal_channels_vt :: Vect_trie -> Nat -> Bool -> [Nat];
extremal_channels_vt a n pol =
  filter
    (\ i ->
      is_member_vt (map (\ j -> not (equal_nat j i == pol)) (upt zero_nat n)) a)
    (upt zero_nat n);

prune_extremal_vt :: Bool -> Nat -> Vect_trie -> Vect_trie;
prune_extremal_vt uu uv VtEmpty = VtEmpty;
prune_extremal_vt True i (VtNode uw a_lo ux) =
  (if equal_nat i zero_nat then a_lo
    else VtNode uw (prune_extremal_vt True (minus_nat i one_nat) a_lo)
           (prune_extremal_vt True (minus_nat i one_nat) ux));
prune_extremal_vt False i (VtNode uy uz a_hi) =
  (if equal_nat i zero_nat then a_hi
    else VtNode uy (prune_extremal_vt False (minus_nat i one_nat) uz)
           (prune_extremal_vt False (minus_nat i one_nat) a_hi));

check_huffman :: (Int -> Proof_step) -> Int -> Proof_step -> Bool;
check_huffman proof_steps step_limit step =
  (case step_witnesses step of {
    HuffmanWitnesses pol witnesses ->
      let {
        width = nat (step_width step);
        widtha = pred width;
        bound = nat (step_bound step);
        a_list = step_vect_list step;
        a = vt_list a_list;
        extremal_channels = extremal_channels_vt a width pol;
        bs = map (\ c -> prune_extremal_vt pol c a) extremal_channels;
        bounds =
          map (\ (x, y) -> get_bound proof_steps step_limit y widtha x)
            (zip bs witnesses);
        huffman_bound = sucmax_value_bound_huffman (Mset (map the bounds));
      } in not (equal_nat width zero_nat) &&
             all (\ xs -> equal_nat (size_list xs) width) a_list &&
               not (null witnesses) &&
                 equal_nat (size_list extremal_channels)
                   (size_list witnesses) &&
                   all (\ b -> not (is_none b)) bounds &&
                     less_eq_nat bound huffman_bound;
    SuccessorWitnesses _ -> False;
  });

check_step :: (Int -> Proof_step) -> Int -> Proof_step -> Bool;
check_step proof_steps step_limit step =
  (case step_witnesses step of {
    HuffmanWitnesses _ _ -> check_huffman proof_steps step_limit step;
    SuccessorWitnesses _ -> check_successors proof_steps step_limit step;
  });

cert_length :: Proof_cert -> Int;
cert_length (ProofCert x1 x2) = x1;

cert_step :: Proof_cert -> Int -> Proof_step;
cert_step (ProofCert x1 x2) = x2;

int_of_nat :: Nat -> Int;
int_of_nat n = Int_of_integer (integer_of_nat n);

all_interval_nat :: (Nat -> Bool) -> Nat -> Nat -> Bool;
all_interval_nat p i j = less_eq_nat j i || p i && all_interval_nat p (suc i) j;

par_range_all :: (Nat -> Bool) -> Nat -> Nat -> Bool;
par_range_all f lo n =
  (if less_nat n (nat_of_integer (1000 :: Integer))
    then all_interval_nat f lo (plus_nat lo n)
    else let {
           na = divide_nat n (nat_of_integer (2 :: Integer));
           a = par_range_all f lo na;
           b = par_range_all f (plus_nat lo na) (minus_nat n na);
         } in par b a && b);

check_proof :: Proof_cert -> Bool;
check_proof cert =
  let {
    steps = cert_step cert;
    n = cert_length cert;
  } in less_eq_int zero_int n &&
         par_range_all
           (\ i -> check_step steps (int_of_nat i) (steps (int_of_nat i)))
           zero_nat (nat n);

one_int :: Int;
one_int = Int_of_integer (1 :: Integer);

minus_int :: Int -> Int -> Int;
minus_int k l = Int_of_integer (integer_of_int k - integer_of_int l);

check_proof_get_bound :: Proof_cert -> Maybe (Int, Int);
check_proof_get_bound cert =
  (if check_proof cert && less_int zero_int (cert_length cert)
    then let {
           last_step = cert_step cert (minus_int (cert_length cert) one_int);
         } in Just (step_width last_step, step_bound last_step)
    else Nothing);

}

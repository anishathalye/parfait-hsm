module K2.Ecdsa.Lemmas

module S = FStar.Seq

let lemma_slice_equal_parts (#a:Type) (s1 s2:S.seq a) (i j k:nat): Lemma
  (requires
    i <= j /\
    j <= k /\
    k <= S.length s1 /\
    k <= S.length s2 /\
    S.equal (S.slice s1 i j) (S.slice s2 i j) /\
    S.equal (S.slice s1 j k) (S.slice s2 j k))
  (ensures
    S.equal (S.slice s1 i k) (S.slice s2 i k)) =
  // assert (forall (i':nat{i' < j - i}). S.index (S.slice s1 i k) i' == S.index (S.slice s1 i j) i');
  // assert (forall (i':nat{i' >= j - i /\ i' < k - i}). S.index (S.slice s1 i k) i' == S.index (S.slice s1 j k) (i' - (j - i)))
  // nicer way of writing the above:
  assert (forall (i':nat{i' < (k - i)}). S.index (S.slice s1 i k) i' ==
    (if i' < j - i then 
       S.index (S.slice s1 i j) i'
     else
       S.index (S.slice s1 j k) (i' - (j - i))))
  // apparently the s2 version is not necessary:
  // assert (forall (i':nat{i' < j - i}). S.index (S.slice s2 i k) i' == S.index (S.slice s2 i j) i');
  // assert (forall (i':nat{i' >= j - i /\ i' < k - i}). S.index (S.slice s2 i k) i' == S.index (S.slice s2 j k) (i' - (j - i)))

(* unused, but I wrote it this way first *)
let lemma_slice_equal_parts' (#a:Type) (s1 s2:S.seq a) (i j k:nat): Lemma
  (requires
    i <= j /\
    j <= k /\
    k <= S.length s1 /\
    k <= S.length s2 /\
    S.equal (S.slice s1 i j) (S.slice s2 i j) /\
    S.equal (S.slice s1 j k) (S.slice s2 j k))
  (ensures
    S.equal (S.slice s1 i k) (S.slice s2 i k)) =
  introduce forall (i':nat{i' < (S.length (S.slice s1 i k))}). S.index (S.slice s1 i k) i' == S.index (S.slice s2 i k) i'
  with if i' < j - i
       then eliminate forall (i'':nat{i'' < S.length (S.slice s1 i j)}). S.index (S.slice s1 i j) i'' == S.index (S.slice s2 i j) i''
            with i'
       else eliminate forall (i'':nat{i'' < S.length (S.slice s1 j k)}). S.index (S.slice s1 j k) i'' == S.index (S.slice s2 j k) i''
            with (i' - (j - i))

val lemma_slice_equal_parts3_full (#a:Type) (s1 s2:S.seq a) (i j:nat): Lemma
  (requires
    i <= j /\
    j <= S.length s1 /\
    S.length s1 = S.length s2 /\
    S.equal (S.slice s1 0 i) (S.slice s2 0 i) /\
    S.equal (S.slice s1 i j) (S.slice s2 i j) /\
    S.equal (S.slice s1 j (S.length s1)) (S.slice s2 j (S.length s1)))
  (ensures S.equal s1 s2)

let lemma_slice_equal_parts3_full #a s1 s2 i j =
  lemma_slice_equal_parts s1 s2 0 i j;
  lemma_slice_equal_parts s1 s2 0 j (S.length s1)

let slice_plus_one #a (s1 s2: S.seq a) (i: nat): Lemma
  (requires (
    i < S.length s1 /\
    i < S.length s2 /\
    S.equal (S.slice s1 0 i) (S.slice s2 0 i) /\
    S.index s1 i == S.index s2 i))
  (ensures (
    S.equal (S.slice s1 0 (i + 1)) (S.slice s2 0 (i + 1))))
  [ SMTPat (S.slice s1 0 (i + 1)); SMTPat (S.slice s2 0 (i + 1)) ]
=
  let x = S.index s1 i in
  let s1' = S.append (S.slice s1 0 i) (S.cons x S.empty) in
  let s2' = S.append (S.slice s2 0 i) (S.cons x S.empty) in
  assert (S.equal s1' (S.slice s1 0 (i + 1)));
  assert (S.equal s2' (S.slice s2 0 (i + 1)))

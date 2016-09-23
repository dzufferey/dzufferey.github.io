(set-option :print-success false)
(set-option :produce-models true)
(set-option :smt.pull-nested-quantifiers true)
(set-option :smt.mbqi true)
(set-logic AUFLIA)

;types
(declare-sort Process 0)
;(declare-sort Value 0)
(declare-sort Set 1)

(declare-fun elem ((Set Process) Process) Bool)
(declare-fun card ((Set Process)) Int)

; consts
(declare-fun HO (Process) (Set Process))
;(declare-fun emptysetP () (Set Process))
(declare-fun n () Int)
(declare-fun decided  () (Set Process))
(declare-fun decided1 () (Set Process))
(declare-fun x  (Process) Int)
(declare-fun x1 (Process) Int)
(declare-fun voting  () (Set Process))
(declare-fun voting1 () (Set Process))

;some (skolem) constants for the invariant
(declare-fun v () Int) ; prophecy variable for the decided value
;(declare-fun A () (Set Process))
;(declare-fun A1 () (Set Process))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(push)
(echo "invariant is inductive")

;no split round:
;∀ i j. ∃ k. k ∈ HO(i) ∧ k ∈ HO(j)
(declare-fun no_split_witness  (Process Process) Process)
(assert
  (forall ((i Process) (j Process))
    (and 
      (elem (HO i) (no_split_witness i j))
      (elem (HO j) (no_split_witness i j))
) ) )

(push)
(echo "round 1, part 1")

;Invariant:
;    ∀ i. ¬decided(i)
;  ∨ ∃ v.  A = { i | x(i) = v }
;    ∧ |A| = n
;    ∧ ∀ i. decided(i) ⇒ x(i) = v
;∧ ∀ i j. voting(i) ∧ voting(j) ⇒ x(i) = x(j)
(assert
  (and
    (forall ((i Process) (j Process))
      (=>
        (and (elem voting i) (elem voting j))
        (= (x i) (x j))))
;    (or
;      (forall ((i Process)) (= (x i) v))
;      (forall ((i Process)) (not (elem decided i))))
) )

;Invariant negated:
;    ∃ i. decided'(i)
;  ∧ ∀ v.  A' = { i | x'(i) = v }
;      ∧   |A'| < n
;        ∨ ∃ i. decided'(i) ∧ x'(i) ≠ v
;∨ ∃ i j. voting(i) ∧ voting(j) ∧ x(i) ≠ x(j)
(declare-fun sk_inv_1 () Process)
(declare-fun sk_inv_2 () Process)
(assert
  (or
    (and
      (elem voting1 sk_inv_1)
      (elem voting1 sk_inv_2)
      (not (= (x1 sk_inv_1) (x1 sk_inv_2))))
;    (and
;      (elem decided1 sk_inv_1)
;      (not (= (x1 sk_inv_2) v)))
) )

;transition relation for round 1
; S: send x to all
; R: x := min received
;    if all same then voting else ¬voting

;min part
(declare-fun min_witness (Process) Process)
(assert
  (forall ((i Process))
    (and
      (= (x1 i) (x (min_witness i)))
      (forall ((j Process))
        (=> (elem (HO i) j) (<= (x1 i) (x j)))
) ) ) )

;voting part
(declare-fun non_voting_witness (Process) Process)
(assert
  (forall ((i Process) (j Process))
    (=> (and (elem voting1 i) (elem (HO i) j)) (= (x1 i) (x j)))
) )
(assert
  (forall ((i Process))
    (=>
      (and
        (not (= (x1 i) (x (non_voting_witness i))))
        (elem (HO i) (non_voting_witness i)))
      (not (elem voting1 i)))
) )

;decided
(assert (= decided decided1))

(check-sat)
;(get-model)
(pop)

(push)
(echo "round 1, part 2")

;Invariant:
;    ∀ i. ¬decided(i)
;  ∨ ∃ v.  A = { i | x(i) = v }
;    ∧ |A| = n
;    ∧ ∀ i. decided(i) ⇒ x(i) = v
;∧ ∀ i j. voting(i) ∧ voting(j) ⇒ x(i) = x(j)
(assert
  (and
;    (forall ((i Process) (j Process))
;      (=>
;        (and (elem voting i) (elem voting j))
;        (= (x i) (x j))))
    (or
      (forall ((i Process)) (= (x i) v))
      (forall ((i Process)) (not (elem decided i))))
) )

;Invariant negated:
;    ∃ i. decided'(i)
;  ∧ ∀ v.  A' = { i | x'(i) = v }
;      ∧   |A'| < n
;        ∨ ∃ i. decided'(i) ∧ x'(i) ≠ v
;∨ ∃ i j. voting(i) ∧ voting(j) ∧ x(i) ≠ x(j)
(declare-fun sk_inv_1 () Process)
(declare-fun sk_inv_2 () Process)
(assert
  (or
;    (and
;      (elem voting1 sk_inv_1)
;      (elem voting1 sk_inv_2)
;      (not (= (x1 sk_inv_1) (x1 sk_inv_2))))
    (and
      (elem decided1 sk_inv_1)
      (not (= (x1 sk_inv_2) v)))
) )

;transition relation for round 1
; S: send x to all
; R: x := min received
;    if all same then voting else ¬voting

;min part
(declare-fun min_witness (Process) Process)
(assert
  (forall ((i Process))
    (and
      (= (x1 i) (x (min_witness i)))
      (forall ((j Process))
        (=> (elem (HO i) j) (<= (x1 i) (x j)))
) ) ) )

;voting part
(declare-fun non_voting_witness (Process) Process)
(assert
  (forall ((i Process) (j Process))
    (=> (and (elem voting1 i) (elem (HO i) j)) (= (x1 i) (x j)))
) )
(assert
  (forall ((i Process))
    (=>
      (and
        (not (= (x1 i) (x (non_voting_witness i))))
        (elem (HO i) (non_voting_witness i)))
      (not (elem voting1 i)))
) )

;decided
(assert (= decided decided1))

(check-sat)
;(get-model)
(pop)


(push)
(echo "round 2")

;Invariant:
;    ∀ i. ¬decided(i)
;  ∨ ∃ v.  A = { i | x(i) = v }
;    ∧ |A| = n
;    ∧ ∀ i. decided(i) ⇒ x(i) = v
;∧ ∀ i j. voting(i) ∧ voting(j) ⇒ x(i) = x(j)
(assert
  (and
;    (forall ((i Process) (j Process))
;      (=>
;        (and (elem voting i) (elem voting j))
;        (= (x i) (x j))))
    (or
      (forall ((i Process)) (= (x i) v))
      (forall ((i Process)) (not (elem decided i))))
) )
;for the prophecy variable
(assert
  (forall ((i Process))
    (=> (elem voting i) (= (x i) v))
  )
)

;Invariant negated:
;    ∃ i. decided'(i)
;  ∧ ∀ v.  A' = { i | x'(i) = v }
;      ∧   |A'| < n
;        ∨ ∃ i. decided'(i) ∧ x'(i) ≠ v
;∨ ∃ i j. voting(i) ∧ voting(j) ∧ x(i) ≠ x(j)
(declare-fun sk_inv_1 () Process)
(declare-fun sk_inv_2 () Process)
(assert
  (or
    (and
      (elem voting1 sk_inv_1)
      (elem voting1 sk_inv_2)
      (not (= (x1 sk_inv_1) (x1 sk_inv_2))))
    (and
      (elem decided1 sk_inv_1)
      (not (= (x1 sk_inv_2) v)))
) )


;transition relation for round 2
; S: send (x,voting) to all
; R: if ∃ voting then x := vote
;    else x := min received
;    if all voting and same then decide

(declare-fun min_or_voting_witness (Process) Process)
(declare-fun non_voting_witness (Process) Process)
(assert
  (forall ((i Process))
    (and
      (= (x1 i) (x (min_or_voting_witness i)))
      (elem (HO i) (min_or_voting_witness i))
      (or
        (elem voting (min_or_voting_witness i)); at least one voting
        (and
          (forall ((j Process))
            (=> (elem (HO i) j)
              (and
                (not (elem voting j)) ;only non voter
                (<= (x1 i) (x j)) ;min
      ) ) ) ) )
      (or
        (and
          (forall ((j Process))
            (=> (elem (HO i) j) (elem voting j))); only voting implies decision
          (elem decided1 i)
        )
        (and
          (not (elem voting (non_voting_witness i))); a non voter
          (elem (HO i) (non_voting_witness i))
          (= (elem decided i) (elem decided1 i))
) ) ) ) )

;voting part
(assert
  (forall ((i Process)) (not (elem voting1 i)) )
)

(check-sat)
;(get-model)
(pop)

(pop)

(push)
(echo "initial state ⇒ invariant")


(assert
  (and
    (forall ((i Process)) (not (elem voting1 i)) )
    (forall ((i Process)) (not (elem decided1 i)) )
  )
)

;Invariant negated:
;    ∃ i. decided'(i)
;  ∧ ∀ v.  A' = { i | x'(i) = v }
;      ∧   |A'| < n
;        ∨ ∃ i. decided'(i) ∧ x'(i) ≠ v
;∨ ∃ i j. voting(i) ∧ voting(j) ∧ x(i) ≠ x(j)
(declare-fun sk_inv_1 () Process)
(declare-fun sk_inv_2 () Process)
(assert
  (or
    (and
      (elem voting1 sk_inv_1)
      (elem voting1 sk_inv_2)
      (not (= (x1 sk_inv_1) (x1 sk_inv_2))))
    (and
      (elem decided1 sk_inv_1)
      (not (= (x1 sk_inv_2) v)))
) )

(check-sat)
;(get-model)
(pop)

(push)
(echo "agreement")

;Invariant:
;    ∀ i. ¬decided(i)
;  ∨ ∃ v.  A = { i | x(i) = v }
;    ∧ |A| = n
;    ∧ ∀ i. decided(i) ⇒ x(i) = v
;∧ ∀ i j. voting(i) ∧ voting(j) ⇒ x(i) = x(j)
(assert
  (and
    (forall ((i Process) (j Process))
      (=>
        (and (elem voting i) (elem voting j))
        (= (x i) (x j))))
    (or
      (forall ((i Process)) (= (x i) v))
      (forall ((i Process)) (not (elem decided i))))
) )


(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (and
    (elem decided sk_i)
    (elem decided sk_j)
    (not (= (x sk_i) (x sk_j)))
  )
)

(check-sat)
;(get-model)
(pop)

(echo "termination")
(push)

(push)
(echo "1st magic round")
;magic round assumption: uniform
(declare-fun sk_HO () (Set Process))
(assert
  (forall ((i Process)) (= (HO i) sk_HO))
)

;transition relation for round 1
; S: send x to all
; R: x := min received
;    if all same then voting else ¬voting

;min part
(declare-fun min_witness (Process) Process)
(assert
  (forall ((i Process))
    (and
      (= (x1 i) (x (min_witness i)))
      (elem (HO i) (min_witness i))
      (forall ((j Process))
        (=> (elem (HO i) j) (<= (x1 i) (x j)))
) ) ) )

;new part in the invariant (negated)
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (not (= (x1 sk_i) (x1 sk_j)))
)

(check-sat)
;(get-model)
(pop)

(push)
(echo "round 2 after magic round")

;invariant
(assert
  (forall ((i Process)) (= (x i) v))
)

;transition relation for round 2
; S: send (x,voting) to all
; R: if ∃ voting then x := vote
;    else x := min received
;    if all voting and same then decide

(declare-fun min_or_voting_witness (Process) Process)
(declare-fun non_voting_witness (Process) Process)
(assert
  (forall ((i Process))
    (and
      (= (x1 i) (x (min_or_voting_witness i)))
      (elem (HO i) (min_or_voting_witness i))
      (or
        (elem voting (min_or_voting_witness i)); at least one voting
        (and
          (forall ((j Process))
            (=> (elem (HO i) j)
              (and
                (not (elem voting j)) ;only non voter
                (<= (x1 i) (x j)) ;min
      ) ) ) ) )
      (or
        (and
          (forall ((j Process))
            (=> (elem (HO i) j) (elem voting j))); only voting implies decision
          (elem decided1 i)
        )
        (and
          (not (elem voting (non_voting_witness i))); a non voter
          (elem (HO i) (non_voting_witness i))
          (= (elem decided i) (elem decided1 i))
) ) ) ) )

;new part in the invariant (negated)
(declare-fun sk_i () (Process))
(assert
  (not (= (x1 sk_i) v))
)

(check-sat)
;(get-model)
(pop)

(push)
(echo "termination invariant is inductive")

(assert
  (forall ((i Process)) (= (x i) v))
)

;transition relation for round 1
; S: send x to all
; R: x := min received
;    if all same then voting else ¬voting

;min part
(declare-fun min_witness (Process) Process)
(assert
  (forall ((i Process))
    (and
      (= (x1 i) (x (min_witness i)))
      (elem (HO i) (min_witness i))
      (forall ((j Process))
        (=> (elem (HO i) j) (<= (x1 i) (x j)))
) ) ) )

;new part in the invariant (negated)
(declare-fun sk_i () (Process))
(assert
  (not (= (x1 sk_i) v))
)

(check-sat)
;(get-model)
(pop)

(push)
(echo "phase after the magic round")

(push)
(echo "round 1")

;invariant new part
(assert
  (forall ((i Process)) (= (x i) v))
)

;transition relation for round 1
; S: send x to all
; R: x := min received
;    if all same then voting else ¬voting

;voting part
(declare-fun non_voting_witness (Process) Process)
(assert
  (forall ((i Process))
    (and
      (= (x1 i) (x i)) ; by the stronger invariant
      ; the version used above is weaker than this one (process may choose not to vote)
      (or
        (and
          (forall ((j Process))
            (=> (elem (HO i) j) (= (x1 i) (x j))))
          (elem voting1 i)
        )
        (and
          (not (= (x1 i) (x (non_voting_witness i))))
          (elem (HO i) (non_voting_witness i))
          (not (elem voting1 i))
        )
      )
    )
  )
)

;new part in the invariant (negated)
(declare-fun sk_i () (Process))
(assert
  (not (elem voting1 sk_i))
)

(check-sat)
;(get-model)
(pop)

(push)
(echo "round 2")

(assert
  (forall ((i Process))
    (and
      (= (x i) v)
      (elem voting i)
    )
  )
)

;transition relation for round 2
; S: send (x,voting) to all
; R: if ∃ voting then x := vote
;    else x := min received
;    if all voting and same then decide

(declare-fun min_or_voting_witness (Process) Process)
(declare-fun non_voting_witness (Process) Process)
(assert
  (forall ((i Process))
    (and
      (= (x1 i) (x (min_or_voting_witness i)))
      (elem (HO i) (min_or_voting_witness i))
      (or
        (elem voting (min_or_voting_witness i)); at least one voting
        (and
          (forall ((j Process))
            (=> (elem (HO i) j)
              (and
                (not (elem voting j)) ;only non voter
                (<= (x1 i) (x j)) ;min
      ) ) ) ) )
      (or
        (and
          (forall ((j Process))
            (=> (elem (HO i) j) (elem voting j))); only voting implies decision
          (elem decided1 i)
        )
        (and
          (not (elem voting (non_voting_witness i))); a non voter
          (elem (HO i) (non_voting_witness i))
          (= (elem decided i) (elem decided1 i))
) ) ) ) )

;new part in the invariant (negated)
(declare-fun sk_i () (Process))
(assert
  (not (elem decided1 sk_i))
)

(check-sat)
;(get-model)
(pop)

(pop)

(push)
(echo "validity")

;assumption
(declare-fun val () Int)
(assert (forall ((p Process)) (= (x p) val) ) )

;to prove
(declare-fun sk_j () (Process))
(assert (elem decided sk_j))
(assert (not (= v val)))

;Invariant:
(assert
  (and
    (forall ((i Process) (j Process))
      (=>
        (and (elem voting i) (elem voting j))
        (= (x i) (x j))))
    (or
      (forall ((i Process)) (= (x i) v))
      (forall ((i Process)) (not (elem decided i))))
) )



(check-sat)
;(get-model)
(pop)

(push)
(echo "integrity")

;Invariant1
(assert
  (and
    (forall ((i Process) (j Process))
      (=>
        (and (elem voting i) (elem voting j))
        (= (x i) (x j))))
    (or
      (forall ((i Process)) (= (x i) v))
      (forall ((i Process)) (not (elem decided i))))
) )

;Invariant2
(assert
  (and
    (forall ((i Process) (j Process))
      (=>
        (and (elem voting1 i) (elem voting1 j))
        (= (x1 i) (x1 j))))
    (or
      (forall ((i Process)) (= (x1 i) v))
      (forall ((i Process)) (not (elem decided1 i))))
) )

;transition relation for round 2
; S: send (x,voting) to all
; R: if ∃ voting then x := vote
;    else x := min received
;    if all voting and same then decide

;decision part
(declare-fun non_voting_witness (Process) Process)
(assert
  (forall ((i Process))
    (or
      (and
        (forall ((j Process)) (=> (elem (HO i) j) (elem voting j)))
        (elem decided1 i) )
      (and
        (elem (HO i) (non_voting_witness i))
        (not (elem voting (non_voting_witness i)))
        (= (elem decided i) (elem decided1 i)) )
    )
  )
)

;to prove
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (or
    (and (elem decided sk_i) (not (elem decided1 sk_i)))
    (and (elem decided sk_j) (not (= (x1 sk_j) (x sk_j))))
) ) 


(check-sat)
;(get-model)
(pop)

(exit)

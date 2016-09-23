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
(declare-fun Coord (Process) Process)
(declare-fun HO (Process) (Set Process))
(declare-fun n () Int)
(declare-fun decided  () (Set Process))
(declare-fun decided1 () (Set Process))
(declare-fun x  (Process) Int)
(declare-fun x1 (Process) Int)
(declare-fun voting  () (Set Process))
(declare-fun voting1 () (Set Process))

;some (skolem) constants for the invariant
(declare-fun v () Int) ; prophecy variable for the decided value


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(push)
(echo "invariant is inductive")

;no split round and well-coord:
;∀ i j. ∃ k. k ∈ HO(i) ∧ k ∈ HO(j)
(declare-fun no_split_witness  (Process Process) Process)
(declare-fun sk_coord () Process)
(assert
  (forall ((i Process) (j Process))
    (and 
      (= (Coord i) sk_coord)
      (elem (HO i) (no_split_witness i j))
      (elem (HO j) (no_split_witness i j))
) ) )

(push)
(echo "round 1")

;Invariant:
;    ∀ i. ¬decided(i)
;  ∨ ∃ v.  A = { i | x(i) = v }
;    ∧ |A| = n
;    ∧ ∀ i. decided(i) ⇒ x(i) = v
(assert
  (and
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
    (and
      (elem voting1 sk_inv_1)
      (elem voting1 sk_inv_2)
      (not (= (x1 sk_inv_1) (x1 sk_inv_2))))
    (and
      (elem decided1 sk_inv_1)
      (not (= (x1 sk_inv_2) v)))
) )

;transition:
; S: coord send x to all
; R: if receive from coord and not decided then set x
(assert
  (forall ((i Process))
    (or
      (and
        (= (Coord i) (Coord (Coord i)))
        (elem (HO i) (Coord i))
        (= (x1 i) (x (Coord i)))
        (elem voting1 i)
      )
      (and
        (or
          (not (= (Coord i) (Coord (Coord i))))
          (not (elem (HO i) (Coord i)))
        )
        (= (x1 i) (x i))
        (not (elem voting1 i))
      )
    )
  )
)

;frame
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
(declare-fun sk_inv_1 () Process)
(declare-fun sk_inv_2 () Process)
(assert
  (or
    (and
      (elem decided1 sk_inv_1)
      (not (= (x1 sk_inv_2) v)))
) )

;transition:
; S: send vote to all
; R: if receive one vote then set x
;    if receive all same then decide

(declare-fun voting_witness (Process) Process)
(declare-fun non_voting_witness (Process) Process)
(assert
  (forall ((i Process))
    (and
      (or
        (and
          (elem (HO i) (voting_witness i))
          (elem voting (voting_witness i)); at least one voting
          (= (x1 i) (x (voting_witness i)))
        )
        (and
          (forall ((j Process))
            (=> (elem (HO i) j)
                (not (elem voting j)))) ;only non voter
          (= (x1 i) (x i))
        )
      )
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


(check-sat)
;(get-model)
(pop)

(pop); end of invariant inductive

(push)
(echo "initial state ⇒ invariant")

;Invariant negated:
;    ∃ i. decided'(i)
;  ∧ ∀ v.  A' = { i | x'(i) = v }
;      ∧   |A'| < n
;        ∨ ∃ i. decided'(i) ∧ x'(i) ≠ v
(declare-fun sk_inv_1 () Process)
(declare-fun sk_inv_2 () Process)
(assert
  (or
    (and
      (elem decided1 sk_inv_1)
      (not (= (x1 sk_inv_2) v)))
) )

(assert
  (and
    (forall ((i Process)) (not (elem voting1 i)) )
    (forall ((i Process)) (not (elem decided1 i)) )
  )
)

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
(assert
  (and
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
    (or
      (forall ((i Process)) (= (x i) v))
      (forall ((i Process)) (not (elem decided i))))
) )

;Invariant2
(assert
  (and
    (or
      (forall ((i Process)) (= (x1 i) v))
      (forall ((i Process)) (not (elem decided1 i))))
) )

;transition relation for round 2
(declare-fun voting_witness (Process) Process)
(declare-fun non_voting_witness (Process) Process)
(assert
  (forall ((i Process))
    (and
      (or
        (and
          (elem (HO i) (voting_witness i))
          (elem voting (voting_witness i)); at least one voting
          (= (x1 i) (x (voting_witness i)))
        )
        (and
          (forall ((j Process))
            (=> (elem (HO i) j)
                (not (elem voting j)))) ;only non voter
          (= (x1 i) (x i))
        )
      )
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

(push)
(echo "termination")

(push)
(echo "magic phase")

;magic round assumption: uniform and well-coordinated
(declare-fun sk_HO () (Set Process))
(declare-fun sk_coord () (Process))
(assert
  (forall ((i Process))
    (and
      (= (Coord i) sk_coord)
      (elem (HO i) (Coord i))
      (= (HO i) sk_HO)
    )
  )
)

(push)
(echo "round 1")

;transition:
; S: coord send x to all
; R: if receive from coord and not decided then set x
(assert
  (forall ((i Process))
    (or
      (and
        (= (Coord i) (Coord (Coord i)))
        (elem (HO i) (Coord i))
        (= (x1 i) (x (Coord i)))
        (elem voting1 i)
      )
      (and
        (or
          (not (= (Coord i) (Coord (Coord i))))
          (not (elem (HO i) (Coord i)))
        )
        (= (x1 i) (x i))
        (not (elem voting1 i))
      )
    )
  )
)

;new part in the invariant (negated)
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (or
    (not (= (x1 sk_i) (x1 sk_j)))
    (not (elem voting1 sk_i))
  )
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
(declare-fun voting_witness (Process) Process)
(declare-fun non_voting_witness (Process) Process)
(assert
  (forall ((i Process))
    (and
      (or
        (and
          (elem (HO i) (voting_witness i))
          (elem voting (voting_witness i)); at least one voting
          (= (x1 i) (x (voting_witness i)))
        )
        (and
          (forall ((j Process))
            (=> (elem (HO i) j)
                (not (elem voting j)))) ;only non voter
          (= (x1 i) (x i))
        )
      )
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

(pop); end of magic phase

(pop); end of termination

(exit)

(set-option :print-success false)
(set-option :produce-models true)
(set-option :smt.mbqi true)
(set-logic AUFLIA)

;types
(declare-sort Process 0)
(declare-sort Value 0)
(declare-sort Set 1)

;cannot have polymorphic function
(declare-fun elemP ((Set Process) Process) Bool)
(declare-fun cardP ((Set Process)) Int)

; consts
(declare-fun Coord (Process Int) Process)
(declare-fun HO (Process Int) (Set Process))
;(declare-fun emptysetP () (Set Process))
(declare-fun n () Int)
(declare-fun r () Int)
(declare-fun r1 () Int)
(declare-fun commit  () (Set Process))
(declare-fun commit1 () (Set Process))
(declare-fun ready  () (Set Process))
(declare-fun ready1 () (Set Process))
(declare-fun decided  () (Set Process))
(declare-fun decided1 () (Set Process))
(declare-fun ts  (Process) Int)
(declare-fun ts1 (Process) Int)
(declare-fun x  (Process) Value)
(declare-fun x1 (Process) Value)
(declare-fun vote (Process) Value)
(declare-fun vote1 (Process) Value)
(declare-fun M (Process) (Set Process))

;some skolem constants for the invariant
(declare-fun sk_v () Value)
(declare-fun sk_t () Int)
(declare-fun sk_A () (Set Process))

;Auxilliary functions
; max function
(declare-fun maxTS ((Set Process)) Process)

(assert
  (forall ((s (Set Process)) (p1 Process) (p2 Process))
    (=>
      (= p1 (maxTS s))
      (and
        (elemP s p1)
        (or
          (not (elemP s p2))
          (<= (ts p2) (ts p1))
        )
      )
    )
  )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(push)
(echo "inductiveness of the invariant")

;//Invariant:
;  ∀ i. ¬decided(i) ∧ ¬ready(i)
;∨ ∃ v, t.   A = { i | ts(i) > t }
;          ∧ |A| > n/2
;          ∧ ∀ i ∈ A. x(i) = v
;          ∧ ∀ i. decided(i) ⇒ x(i) = v
;          ∧ ∀ i. commit(i) ⇒ vote(i) = v
;          ∧ ∀ i. ready(i) ⇒ vote(i) = v
;          ∧ t ≤ Φ
;          ∧ ∀ i. ts(i) = Φ ⇒ commit(Coord(i))
(assert
  (or
    (forall ((i Process))
      (and
        (not (elemP decided i))
        (not (elemP ready i))
      )
    )
    (and
      (> (* 2 (cardP sk_A)) n)
      (<= sk_t r)
      (forall ((i Process))
        (and
          (= (elemP sk_A i) (>= (ts i) sk_t))
          (=> (elemP sk_A i) (= (x i) sk_v))
          (=> (elemP commit i) (= (vote i) sk_v))
          (=> (elemP decided i) (= (x i) sk_v))
          (=> (elemP ready i) (= (vote i) sk_v))
          (=> (= (ts i) r) (elemP commit (Coord i r))) 
) ) ) ) )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;//Invariant negated:
;  ∃ i. decided′(i) ∨ ready′(i)
;∧ ∀ v, t. ( A′ = { i | ts(i) > t }
;          ∧ ( |A′| ≤ n/2
;            ∨ ∃ i ∈ A′. x′(i) ≠ v )
;          )
;          ∨ ∃ i. commit′(i) ∧ vote(i) ≠ v
;          ∨ ∃ i. ready′(i) ∧ x′(i) ≠ v
;          ∨ ∃ i. decided′(i) ∧ x′(i) ≠ v
;          ∨ t > Φ
;          ∨ ∃ i. ts1(i) = Φ ∧ ¬commit'(Coord(i))
(declare-fun sk_A1 () (Set Process))
(declare-fun sk_i () (Process))
(assert
  (and
    (exists ((i Process))
      (or
        (elemP decided1 i)
        (elemP ready1 i)
      )
    )
;definition of A'
    (forall ((j Process)) (= (elemP sk_A1 j) (>= (ts1 j) sk_t)))
;relating the cardinalities of A and A′
    (=> (forall ((i Process)) (=> (elemP sk_A i) (elemP sk_A1 i))) (<= (cardP sk_A) (cardP sk_A1)))
;v, t instantiated to be equal to sk_v, sk_t
      (or
;negation of the constraints over A
        (<= (* 2 (cardP sk_A1)) n)
        (and (elemP sk_A1 sk_i) (not (= (x1 sk_i) sk_v)))
;better when skolemized ... 
        (and (elemP commit1 sk_i) (not (= (vote1 sk_i) sk_v)))
        (> sk_t r1)
        (and (elemP decided1 sk_i) (not (= (x1 sk_i) sk_v)))
        (and (elemP ready1 sk_i) (not (= (vote1 sk_i) sk_v)))
        (and (= (ts1 sk_i) r1) (not (elemP commit1 (Coord sk_i r))))
      )
  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;phase 1
(push)
(echo "phase 1")

;populating the mailbox
;∀ i j ∈ P. (i, x(i), ts(i)) ∈ M(j) ⇔ j = Coord(i, Φ) ∧ i ∈ HO(j, Φ)
(assert
  (forall ((i Process) (j Process))
    (= (elemP (M j) i) (and (= j (Coord i r)) (elemP (HO j r) i)))))

;update local state case 1:
;∀ i ∈ P. i = Coord(i, Φ) ∧ |M(i)| > n/2 ⇒ 
;    Θ = max { t | ∃ j, v. (j, v, t) ∈ M(j) }
;  ∧ vote(i) ∈ { v | ∃ j. (j, v, Θ) ∈ M(j) }
;  ∧ commit(i)
(assert
  (forall ((i Process))
    (=>
      (and
        (= i (Coord i r))
        (> (* 2 (cardP (M i))) n))
      (exists ((j Process))
        (and
          (= j (maxTS (M i)))
          (= (vote1 i) (x j))
          (elemP commit1 i)
        )))))
 
;update local state case 2:
;∀ i ∈ P. i ≠ Coord(i, Φ) ∨ |M(j)| ≤ n/2 ⇒ 
;    ¬commit(i)
(assert
  (forall ((i Process))
    (or
      (and
        (= i (Coord i r))
        (> (* 2 (cardP (M i))) n)
      )
      (and
        (= (elemP commit i) (elemP commit1 i))
        (= (vote1 i) (vote i))
      )
)))

;frame
(assert
  (and
    (= r r1)
    (= decided decided1)
    (= ready ready1)
    (forall ((i Process))
      (and
        (= (ts i) (ts1 i))
        (= (x i) (x1 i))
))))

; constraints for set cardinality:
; A    = { p | ts(p) >= t }
; M(c) = { p | p ∈ HO(c) ∧ c = Coord(p) }
(declare-fun tt (Process) Int) 
(declare-fun tf (Process) Int) 
(declare-fun ft (Process) Int) 
(declare-fun ff (Process) Int) 

(assert
  (forall ((p Process))
    (and
      (>= (tt p) 0)
      (>= (tf p) 0)
      (>= (ft p) 0)
      (>= (ff p) 0)
      (= (+ (tt p) (tf p) (ft p) (ff p)) n)
      (= (cardP (M p)) (+ (tt p) (ft p)))
      (= (cardP sk_A) (+ (tt p) (tf p)))
; witnesses
      (=> (> (tt p) 0) (exists ((p2 Process)) (and      (elemP sk_A p2)       (elemP (M p) p2)  )))
      (=> (> (tf p) 0) (exists ((p2 Process)) (and      (elemP sk_A p2)  (not (elemP (M p) p2)) )))
      (=> (> (ft p) 0) (exists ((p2 Process)) (and (not (elemP sk_A p2))      (elemP (M p) p2)  )))
      (=> (> (ff p) 0) (exists ((p2 Process)) (and (not (elemP sk_A p2)) (not (elemP (M p) p2)) )))
    )
  )
)

(check-sat)
;(get-model)
(pop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;phase 2
(push)
(echo "phase 2")

;//messages are triples (i, v, j)

;populating the mailbox
;∀ i j ∈ P. (i, vote(i)) ∈ M′(j) ⇔ i = Coord(i, Φ) ∧ commit(i) ∧ i ∈ HO(j, Φ+1)
(assert
  (forall ((i Process) (j Process))
    (= (elemP (M j) i) (and (= i (Coord i r)) (elemP commit i) (elemP (HO j r) i)))))

;update: case 1 (true branch)
;∀ i ∈ P.
;    N(i) = { v | (Coord(i, Φ), v) ∈ M′(i) }
;  ∧ ( ( (x′(i) ∈ N(i) ∧ ts′(i) = Φ)
;    ∨ ( N(i) = ∅ ∧ x′(i) = x(i) ∧ ts′(i) = ts(i) )
;    )
(assert
  (forall ((i Process))
    (exists ((j Process))
      (=>
        (and
          (elemP (M i) j)
          (= j (Coord i r))
        )
        (and
          (= (ts1 i) r)
          (= (x1 i) (vote j))
        )
      )
    )
  )
)

;update: case 2 (false branch)
(assert
  (forall ((i Process) (j Process))
    (or
      (and
        (elemP (M i) j)
        (= j (Coord i r))
      )
      (and
        (= (ts1 i) (ts i))
        (= (x1 i) (x i))
      )
    )
  )
)

;frame
(assert
  (and
    (= r r1)
    (= decided decided1)
    (= ready ready1)
    (= commit commit1)
    (forall ((i Process))
        (= (vote i) (vote1 i))
    )
  )
)

(check-sat)
;(get-model)
(pop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;phase 3
(push)
(echo "phase 3")

;//messages are pairs (i, j)
;
;populating the mailbox
;∀ i j ∈ P. i ∈ M″(j) ⇔ j = Coord(i, Φ) ∧ ts′(i) = Φ ∧ i ∈ HO(j, Φ+2)
(assert
  (forall ((i Process) (j Process))
    (=
      (elemP (M j) i)
      (and (= j (Coord i r)) (elemP (HO j r) i) (= (ts i) r)))))

;update: case 1 (true branch)
;∀ i ∈ P. i = Coord(i, Φ) ∧ |M(j)| > n/2 ⇒ ready(i)
(assert
  (forall ((i Process))
    (=>
      (and
        (= i (Coord i r))
        (> (* 2 (cardP (M i))) n)
      )
      (elemP ready1 i)
    )
  )
)

;update: case 2 (false branch)
;∀ i ∈ P. i ≠ Coord(i, Φ) ∨ |M(j)| ≤ n/2 ⇒ ¬ready(i)
(assert
  (forall ((i Process))
    (or
      (and
        (= i (Coord i r))
        (> (* 2 (cardP (M i))) n)
      )
      (= (elemP ready i) (elemP ready1 i))
    )
  )
)

;update: frame
(assert
  (and
    (= r r1)
    (= decided decided1)
    (= commit commit1)
    (forall ((i Process))
      (and
        (= (vote i) (vote1 i))
        (= (ts i) (ts1 i))
        (= (x i) (x1 i))
))))


(check-sat)
;(get-model)
(pop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;phase 4
(push)
(echo "phase 4")

;//messages are triples (i, v, j)
;
;populating the mailboxes
;∀ i j ∈ P. (i, vote(i)) ∈ M‴(j) ⇔ i = Coord(i, Φ) ∧ ready(i) ∧ i ∈ HO(j, Φ+3)

;update
;∀ i ∈ P. 
;    N′(i) = { v | (Coord(i, Φ), v) ∈ M‴(j) }
;  ∧ (N′(i) = ∅ ⇒ decided′(i) = decided(i))
;  ∧ (N′(i) ≠ ∅ ⇒ decided′(i))

;update case 1a
(assert
  (forall ((i Process))
    (exists ((j Process))
      (=>
        (and
          (= j (Coord j r))
          (elemP ready j)
          (elemP (HO i r) j)
          (= j (Coord i r))
        )
        (and
          (elemP decided1 i)
          (= (x1 i) (vote j))
        )
      )
    )
  )
)

;update case 2a
(assert
  (forall ((i Process) (j Process))
    (or
      (and
        (= j (Coord j r))
        (elemP ready j)
        (elemP (HO i r) j)
        (= j (Coord i r))
      )
      (and
        (= (elemP decided i) (elemP decided1 i))
        (= (x1 i) (x i))
      )
    )
  )
)


;update case 1b
(assert
  (forall ((i Process))
;    (=>
;      (= i (Coord i r))
      (and
        (not (elemP ready1 i))
        (not (elemP commit1 i))
      )
;    )
  )
)

;update case 2b
;(assert
;  (forall ((i Process))
;    (or
;      (= i (Coord i r))
;      (and
;        (= (elemP ready i) (elemP ready1 i))
;        (= (elemP commit i) (elemP commit1 i))
;      )
;    )
;  )
;)

;update frame
(assert
  (and
    (= r1 (+ r 1))
    (forall ((i Process))
      (and
        (= (ts i) (ts1 i))
        (= (vote i) (vote1 i))
))))

(check-sat)
;(get-model)
(pop)

(pop)

;inital state implies the invariant
(push)
(echo "the inital state implies the invariant")

(assert
  (and
    (= 0 r)
    (forall ((j Process))
      (and
        (= 0 (ts j))
        (not (elemP decided j))
        (not (elemP commit j))
        (not (elemP ready j))
      )
    )
  )
)


;//Invariant negated:
;  ∃ i. decided′(i) ∨ ready′(i)
;∧ ∀ v, t. ( A′ = { i | ts(i) > t }
;          ∧ ( |A′| ≤ n/2
;            ∨ ∃ i ∈ A′. x′(i) ≠ v )
;          )
;          ∨ ∃ i. commit′(i) ∧ vote(i) ≠ v
;          ∨ ∃ i. ready′(i) ∧ x′(i) ≠ v
;          ∨ ∃ i. decided′(i) ∧ x′(i) ≠ v
;          ∨ t > Φ
;          ∨ ∃ i. ts'(i) = Φ ∧ ¬commit'(Coord(i))
(declare-fun sk_A1 () (Set Process))
(declare-fun sk_i () (Process))
(assert
  (and
    (exists ((i Process))
      (or
        (elemP decided i)
        (elemP ready i)
      )
    )
;definition of A'
    (forall ((j Process)) (= (elemP sk_A1 j) (>= (ts j) sk_t)))
;v, t instantiated to be equal to sk_v, sk_t
      (or
;negation of the constraints over A
        (<= (* 2 (cardP sk_A1)) n)
        (and (elemP sk_A1 sk_i) (not (= (x sk_i) sk_v)))
;better when skolemized ... 
        (and (elemP commit sk_i) (not (= (vote sk_i) sk_v)))
        (> sk_t r)
        (and (elemP decided sk_i) (not (= (x sk_i) sk_v)))
        (and (elemP ready sk_i) (not (= (vote sk_i) sk_v)))
        (and (= (ts sk_i) r) (not (elemP commit (Coord sk_i r))))
      )
  )
)
(check-sat)
;(get-model)
(pop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;-agreement
(push)
(echo "argreement")

;//Invariant:
;  ∀ i. ¬decided(i) ∧ ¬ready(i)
;∨ ∃ v, t.   A = { i | ts(i) > t }
;          ∧ |A| > n/2
;          ∧ ∀ i ∈ A. x(i) = v
;          ∧ ∀ i. decided(i) ⇒ x(i) = v
;          ∧ ∀ i. commit(i) ⇒ vote(i) = v
;          ∧ ∀ i. ready(i) ⇒ vote(i) = v
;          ∧ t ≤ Φ
;          ∧ ∀ i. ts(i) = Φ ⇒ commit(Coord(i))
(assert
  (or
    (forall ((i Process))
      (and
        (not (elemP decided i))
        (not (elemP ready i))
      )
    )
    (and
      (> (* 2 (cardP sk_A)) n)
      (<= sk_t r)
      (forall ((i Process))
        (and
          (= (elemP sk_A i) (>= (ts i) sk_t))
          (=> (elemP sk_A i) (= (x i) sk_v))
          (=> (elemP commit i) (= (vote i) sk_v))
          (=> (elemP decided i) (= (x i) sk_v))
          (=> (elemP ready i) (= (vote i) sk_v))
          (=> (= (ts i) r) (elemP commit (Coord i r))) 
) ) ) ) )

(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (and
    (elemP decided sk_i)
    (elemP decided sk_j)
    (not (= (x sk_i) (x sk_j)))
  )
)

(check-sat)
;(get-model)
(pop)

;-termination (all processes are decided)
(push)
(echo "termination")

(declare-fun sk_c () (Process))
(assert
  (and
    (forall ((i Process))
      (and
        (= sk_c (Coord i r))
        (elemP (HO i r) sk_c)
      )
    )
    (> (* 2 (cardP (HO sk_c r))) n)
  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;phase 1
(push)
(echo "phase 1")

;populating the mailbox
;∀ i j ∈ P. (i, x(i), ts(i)) ∈ M(j) ⇔ j = Coord(i, Φ) ∧ i ∈ HO(j, Φ)
(assert
  (forall ((i Process) (j Process))
    (= (elemP (M j) i) (and (= j (Coord i r)) (elemP (HO j r) i)))))

;update local state case 1:
;∀ i ∈ P. i = Coord(i, Φ) ∧ |M(i)| > n/2 ⇒ 
;    Θ = max { t | ∃ j, v. (j, v, t) ∈ M(j) }
;  ∧ vote(i) ∈ { v | ∃ j. (j, v, Θ) ∈ M(j) }
;  ∧ commit(i)
(assert
  (forall ((i Process))
    (=>
      (and
        (= i (Coord i r))
        ;(> (* 2 (cardP (M i))) n)
      )
      (exists ((j Process))
        (and
          (= j (maxTS (M i)))
          (= (vote1 i) (x j))
          (elemP commit1 i)
        )))))
 
;update local state case 2:
;∀ i ∈ P. i ≠ Coord(i, Φ) ∨ |M(j)| ≤ n/2 ⇒ 
;    ¬commit(i)
(assert
  (forall ((i Process))
    (or
      (and
        (= i (Coord i r))
        ;(> (* 2 (cardP (M i))) n)
      )
      (and
        (= (elemP commit i) (elemP commit1 i))
        (= (vote1 i) (vote i))
      )
)))

;frame
(assert
  (and
    (= r r1)
    (= decided decided1)
    (= ready ready1)
    (forall ((i Process))
      (and
        (= (ts i) (ts1 i))
        (= (x i) (x1 i))
))))

;//Invariant negated (new part):
(assert (not (elemP commit1 sk_c)))

(check-sat)
;(get-model)
(pop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;phase 2
(push)
(echo "phase 2")

;//Invariant:
(assert (elemP commit sk_c))


;populating the mailbox
;∀ i j ∈ P. (i, vote(i)) ∈ M′(j) ⇔ i = Coord(i, Φ) ∧ commit(i) ∧ i ∈ HO(j, Φ+1)
(assert
  (forall ((i Process) (j Process))
    (= (elemP (M j) i) (and (= i (Coord i r)) (elemP commit i) (elemP (HO j r) i)))))

;update: case 1 (true branch)
;∀ i ∈ P.
;    N(i) = { v | (Coord(i, Φ), v) ∈ M′(i) }
;  ∧ ( ( (x′(i) ∈ N(i) ∧ ts′(i) = Φ)
;    ∨ ( N(i) = ∅ ∧ x′(i) = x(i) ∧ ts′(i) = ts(i) )
;    )
(assert
  (forall ((i Process))
    (=>
      (elemP (M i) (Coord i r))
      (and
        (= (ts1 i) r)
        (= (x1 i) (vote (Coord i r)))
      )
    )
  )
)

;update: case 2 (false branch)
;(assert
;  (forall ((i Process) (j Process))
;    (or
;      (and
;        (elemP (M i) j)
;        (= j (Coord i r))
;      )
;      (and
;        (= (ts1 i) (ts i))
;        (= (x1 i) (x i))
;      )
;    )
;  )
;)

;frame
(assert
  (and
    (= r r1)
    (= decided decided1)
    (= ready ready1)
    (= commit commit1)
    (forall ((i Process))
        (= (vote i) (vote1 i))
    )
  )
)

;Invariant negated (new part)
(declare-fun sk_i () (Process))
(assert
  (or
    (not (= (ts1 sk_i) r1))
    (not (= (x1 sk_i) (vote sk_c)))
  )
)

(check-sat)
;(get-model)
(pop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;phase 3
(push)
(echo "phase 3")

;//Invariant:
(assert
  (or
    (forall ((i Process))
        (not (elemP decided i))
    )
    (and
      (> (* 2 (cardP sk_A)) n)
      (<= sk_t r)
      (forall ((i Process))
        (and
          (= (elemP sk_A i) (>= (ts i) sk_t))
          (=> (elemP sk_A i) (= (x i) sk_v))
          (=> (elemP commit i) (= (vote i) sk_v))
          (=> (= (ts i) r) (elemP commit (Coord i r))) 
) ) ) ) )
(assert (elemP commit sk_c))
(assert
  (forall ((i Process))
    (and
      (= (ts i) r)
      (= (x i) sk_v)
    )
  )
)


;//messages are pairs (i, j)
;
;populating the mailbox
;∀ i j ∈ P. i ∈ M″(j) ⇔ j = Coord(i, Φ) ∧ ts′(i) = Φ ∧ i ∈ HO(j, Φ+2)
(assert
  (forall ((i Process) (j Process))
    (=
      (elemP (M j) i)
      (and (= j (Coord i r)) (elemP (HO j r) i) (= (ts i) r)))))

;update: case 1 (true branch)
;∀ i ∈ P. i = Coord(i, Φ) ∧ |M(j)| > n/2 ⇒ ready(i)
(assert
  (forall ((i Process))
    (=>
      (and
        (= i (Coord i r))
        (> (* 2 (cardP (M i))) n)
      )
      (elemP ready1 i)
    )
  )
)

;update: case 2 (false branch)
;∀ i ∈ P. i ≠ Coord(i, Φ) ∨ |M(j)| ≤ n/2 ⇒ ¬ready(i)
(assert
  (forall ((i Process))
    (or
      (and
        (= i (Coord i r))
        (> (* 2 (cardP (M i))) n)
      )
      (= (elemP ready i) (elemP ready1 i))
    )
  )
)

;update: frame
(assert
  (and
    (= r r1)
    (= decided decided1)
    (= commit commit1)
    (forall ((i Process))
      (and
        (= (vote i) (vote1 i))
        (= (ts i) (ts1 i))
        (= (x i) (x1 i))
))))

;//Invariant negated (new part)
(assert (not (elemP ready1 sk_c)))

(check-sat)
;(get-model)
(pop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;phase 4
(push)
(echo "phase 4")

;//Invariant:
(assert
    (and
      (> (* 2 (cardP sk_A)) n)
      (<= sk_t r)
      (forall ((i Process))
        (and
          (= (elemP sk_A i) (>= (ts i) sk_t))
          (=> (elemP sk_A i) (= (x i) sk_v))
          (=> (elemP commit i) (= (vote i) sk_v))
          (=> (= (ts i) r) (elemP commit (Coord i r))) 
) ) ) )
(assert (elemP commit sk_c))
(assert (elemP ready sk_c))
(assert
  (forall ((i Process))
    (and
      (= (ts i) r)
      (= (x i) sk_v)
    )
  )
)

;
;populating the mailboxes
;∀ i j ∈ P. (i, vote(i)) ∈ M‴(j) ⇔ i = Coord(i, Φ) ∧ ready(i) ∧ i ∈ HO(j, Φ+3)

;update
;∀ i ∈ P. 
;    N′(i) = { v | (Coord(i, Φ), v) ∈ M‴(j) }
;  ∧ (N′(i) = ∅ ⇒ decided′(i) = decided(i))
;  ∧ (N′(i) ≠ ∅ ⇒ decided′(i))

;update case 1a
(assert
  (forall ((i Process))
    (exists ((j Process))
      (=>
        (and
          (= j (Coord j r))
          (elemP ready j)
          (elemP (HO i r) j)
          (= j (Coord i r))
        )
        (and
          (elemP decided1 i)
          (= (x1 i) (vote j))
        )
      )
    )
  )
)

;update case 2a
(assert
  (forall ((i Process) (j Process))
    (or
      (and
        (= j (Coord j r))
        (elemP ready j)
        (elemP (HO i r) j)
        (= j (Coord i r))
      )
      (and
        (= (elemP decided i) (elemP decided1 i))
        (= (x1 i) (x i))
      )
    )
  )
)


;update case 1b
(assert
  (forall ((i Process))
;    (=>
;      (= i (Coord i r))
      (and
        (not (elemP ready1 i))
        (not (elemP commit1 i))
      )
;    )
  )
)

;update case 2b
;(assert
;  (forall ((i Process))
;    (or
;      (= i (Coord i r))
;      (and
;        (= (elemP ready i) (elemP ready1 i))
;        (= (elemP commit i) (elemP commit1 i))
;      )
;    )
;  )
;)

;update frame
(assert
  (and
    (= r1 (+ r 1))
    (forall ((i Process))
      (and
        (= (ts i) (ts1 i))
        (= (vote i) (vote1 i))
))))

;//goal:
(declare-fun sk_i () (Process))
(assert
  (not (elemP decided1 sk_i))
)

(check-sat)
;(get-model)
(pop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(push)
(echo "validity")

;assumption
(declare-fun val () Value)
(assert (forall ((p Process)) (= (x p) val) ) )

;//Invariant:
;  ∀ i. ¬decided(i) ∧ ¬ready(i)
;∨ ∃ v, t.   A = { i | ts(i) > t }
;          ∧ |A| > n/2
;          ∧ ∀ i ∈ A. x(i) = v
;          ∧ ∀ i. decided(i) ⇒ x(i) = v
;          ∧ ∀ i. commit(i) ⇒ vote(i) = v
;          ∧ ∀ i. ready(i) ⇒ vote(i) = v
;          ∧ t ≤ Φ
;          ∧ ∀ i. ts(i) = Φ ⇒ commit(Coord(i))
(assert
  (or
    (forall ((i Process))
      (and
        (not (elemP decided i))
        (not (elemP ready i))
      )
    )
    (and
      (> (* 2 (cardP sk_A)) n)
      (<= sk_t r)
      (forall ((i Process))
        (and
          (= (elemP sk_A i) (>= (ts i) sk_t))
          (=> (elemP sk_A i) (= (x i) sk_v))
          (=> (elemP commit i) (= (vote i) sk_v))
          (=> (elemP decided i) (= (x i) sk_v))
          (=> (elemP ready i) (= (vote i) sk_v))
          (=> (= (ts i) r) (elemP commit (Coord i r))) 
) ) ) ) )

;to prove:
(declare-fun sk_j () (Process))
(assert (elemP decided sk_j))
(assert (not (= (x sk_j) val) ) )

(check-sat)
;(get-model)
(pop)

(push)
(echo "integrity")

;to prove
(declare-fun sk_i () (Process))
(declare-fun sk_j () (Process))
(assert
  (or
    (forall ((p Process)) (not (= (x1 sk_j) (x p))))
    (and (elemP decided sk_i) (not (elemP decided1 sk_i)))
    (and (elemP decided sk_j) (not (= (x1 sk_j) (x sk_j))))
) ) 

;//Invariant:
;  ∀ i. ¬decided(i) ∧ ¬ready(i)
;∨ ∃ v, t.   A = { i | ts(i) > t }
;          ∧ |A| > n/2
;          ∧ ∀ i ∈ A. x(i) = v
;          ∧ ∀ i. decided(i) ⇒ x(i) = v
;          ∧ ∀ i. commit(i) ⇒ vote(i) = v
;          ∧ ∀ i. ready(i) ⇒ vote(i) = v
;          ∧ t ≤ Φ
;          ∧ ∀ i. ts(i) = Φ ⇒ commit(Coord(i))
(assert
  (or
    (forall ((i Process))
      (and
        (not (elemP decided i))
        (not (elemP ready i))
      )
    )
    (and
      (> (* 2 (cardP sk_A)) n)
      (<= sk_t r)
      (forall ((i Process))
        (and
          (= (elemP sk_A i) (>= (ts i) sk_t))
          (=> (elemP sk_A i) (= (x i) sk_v))
          (=> (elemP commit i) (= (vote i) sk_v))
          (=> (elemP decided i) (= (x i) sk_v))
          (=> (elemP ready i) (= (vote i) sk_v))
          (=> (= (ts i) r) (elemP commit (Coord i r))) 
) ) ) ) )

(push)
(echo "phase 1")

;populating the mailbox
;∀ i j ∈ P. (i, x(i), ts(i)) ∈ M(j) ⇔ j = Coord(i, Φ) ∧ i ∈ HO(j, Φ)
(assert
  (forall ((i Process) (j Process))
    (= (elemP (M j) i) (and (= j (Coord i r)) (elemP (HO j r) i)))))

;update local state case 1:
;∀ i ∈ P. i = Coord(i, Φ) ∧ |M(i)| > n/2 ⇒ 
;    Θ = max { t | ∃ j, v. (j, v, t) ∈ M(j) }
;  ∧ vote(i) ∈ { v | ∃ j. (j, v, Θ) ∈ M(j) }
;  ∧ commit(i)
(assert
  (forall ((i Process))
    (=>
      (and
        (= i (Coord i r))
        (> (* 2 (cardP (M i))) n))
      (exists ((j Process))
        (and
          (= j (maxTS (M i)))
          (= (vote1 i) (x j))
          (elemP commit1 i)
        )))))
 
;update local state case 2:
;∀ i ∈ P. i ≠ Coord(i, Φ) ∨ |M(j)| ≤ n/2 ⇒ 
;    ¬commit(i)
(assert
  (forall ((i Process))
    (or
      (and
        (= i (Coord i r))
        (> (* 2 (cardP (M i))) n)
      )
      (and
        (= (elemP commit i) (elemP commit1 i))
        (= (vote1 i) (vote i))
      )
)))

;frame
(assert
  (and
    (= r r1)
    (= decided decided1)
    (= ready ready1)
    (forall ((i Process))
      (and
        (= (ts i) (ts1 i))
        (= (x i) (x1 i))
))))

; constraints for set cardinality:
; A    = { p | ts(p) >= t }
; M(c) = { p | p ∈ HO(c) ∧ c = Coord(p) }
(declare-fun tt (Process) Int) 
(declare-fun tf (Process) Int) 
(declare-fun ft (Process) Int) 
(declare-fun ff (Process) Int) 

(assert
  (forall ((p Process))
    (and
; BAPA reduction
      (>= (tt p) 0)
      (>= (tf p) 0)
      (>= (ft p) 0)
      (>= (ff p) 0)
      (= (+ (tt p) (tf p) (ft p) (ff p)) n)
      (= (cardP (M p)) (+ (tt p) (ft p)))
      (= (cardP sk_A) (+ (tt p) (tf p)))
; witnesses
      (=> (> (tt p) 0) (exists ((p2 Process)) (and      (elemP sk_A p2)       (elemP (M p) p2)  )))
      (=> (> (tf p) 0) (exists ((p2 Process)) (and      (elemP sk_A p2)  (not (elemP (M p) p2)) )))
      (=> (> (ft p) 0) (exists ((p2 Process)) (and (not (elemP sk_A p2))      (elemP (M p) p2)  )))
      (=> (> (ff p) 0) (exists ((p2 Process)) (and (not (elemP sk_A p2)) (not (elemP (M p) p2)) )))
    )
  )
)

(check-sat)
;(get-model)
(pop)

(push)
(echo "phase 2")

;populating the mailbox
;∀ i j ∈ P. (i, vote(i)) ∈ M′(j) ⇔ i = Coord(i, Φ) ∧ commit(i) ∧ i ∈ HO(j, Φ+1)
(assert
  (forall ((i Process) (j Process))
    (= (elemP (M j) i) (and (= i (Coord i r)) (elemP commit i) (elemP (HO j r) i)))))

;update: case 1 (true branch)
;∀ i ∈ P.
;    N(i) = { v | (Coord(i, Φ), v) ∈ M′(i) }
;  ∧ ( ( (x′(i) ∈ N(i) ∧ ts′(i) = Φ)
;    ∨ ( N(i) = ∅ ∧ x′(i) = x(i) ∧ ts′(i) = ts(i) )
;    )
(assert
  (forall ((i Process))
    (=>
      (elemP (M i) (Coord i r))
      (and
        (= (ts1 i) r)
        (= (x1 i) (vote (Coord i r)))
      )
    )
  )
)

;update: case 2 (false branch)
;(assert
;  (forall ((i Process) (j Process))
;    (or
;      (and
;        (elemP (M i) j)
;        (= j (Coord i r))
;      )
;      (and
;        (= (ts1 i) (ts i))
;        (= (x1 i) (x i))
;      )
;    )
;  )
;)

;frame
(assert
  (and
    (= r r1)
    (= decided decided1)
    (= ready ready1)
    (= commit commit1)
    (forall ((i Process))
        (= (vote i) (vote1 i))
    )
  )
)

(check-sat)
;(get-model)
(pop)

(push)
(echo "phase 3")

;populating the mailbox
;∀ i j ∈ P. i ∈ M″(j) ⇔ j = Coord(i, Φ) ∧ ts′(i) = Φ ∧ i ∈ HO(j, Φ+2)
(assert
  (forall ((i Process) (j Process))
    (=
      (elemP (M j) i)
      (and (= j (Coord i r)) (elemP (HO j r) i) (= (ts i) r)))))

;update: case 1 (true branch)
;∀ i ∈ P. i = Coord(i, Φ) ∧ |M(j)| > n/2 ⇒ ready(i)
(assert
  (forall ((i Process))
    (=>
      (and
        (= i (Coord i r))
        (> (* 2 (cardP (M i))) n)
      )
      (elemP ready1 i)
    )
  )
)

;update: case 2 (false branch)
;∀ i ∈ P. i ≠ Coord(i, Φ) ∨ |M(j)| ≤ n/2 ⇒ ¬ready(i)
(assert
  (forall ((i Process))
    (or
      (and
        (= i (Coord i r))
        (> (* 2 (cardP (M i))) n)
      )
      (= (elemP ready i) (elemP ready1 i))
    )
  )
)

;update: frame
(assert
  (and
    (= r r1)
    (= decided decided1)
    (= commit commit1)
    (forall ((i Process))
      (and
        (= (vote i) (vote1 i))
        (= (ts i) (ts1 i))
        (= (x i) (x1 i))
))))

(check-sat)
;(get-model)
(pop)

(push)
(echo "phase 4")

;
;populating the mailboxes
;∀ i j ∈ P. (i, vote(i)) ∈ M‴(j) ⇔ i = Coord(i, Φ) ∧ ready(i) ∧ i ∈ HO(j, Φ+3)

;update
;∀ i ∈ P. 
;    N′(i) = { v | (Coord(i, Φ), v) ∈ M‴(j) }
;  ∧ (N′(i) = ∅ ⇒ decided′(i) = decided(i))
;  ∧ (N′(i) ≠ ∅ ⇒ decided′(i))

;update case 1a
(assert
  (forall ((i Process))
    (exists ((j Process))
      (=>
        (and
          (= j (Coord j r))
          (elemP ready j)
          (elemP (HO i r) j)
          (= j (Coord i r))
        )
        (and
          (elemP decided1 i)
          (= (x1 i) (vote j))
        )
      )
    )
  )
)

;update case 2a
(assert
  (forall ((i Process) (j Process))
    (or
      (and
        (= j (Coord j r))
        (elemP ready j)
        (elemP (HO i r) j)
        (= j (Coord i r))
      )
      (and
        (= (elemP decided i) (elemP decided1 i))
        (= (x1 i) (x i))
      )
    )
  )
)


;update case 1b
(assert
  (forall ((i Process))
;    (=>
;      (= i (Coord i r))
      (and
        (not (elemP ready1 i))
        (not (elemP commit1 i))
      )
;    )
  )
)

;update case 2b
;(assert
;  (forall ((i Process))
;    (or
;      (= i (Coord i r))
;      (and
;        (= (elemP ready i) (elemP ready1 i))
;        (= (elemP commit i) (elemP commit1 i))
;      )
;    )
;  )
;)

;update frame
(assert
  (and
    (= r1 (+ r 1))
    (forall ((i Process))
      (and
        (= (ts i) (ts1 i))
        (= (vote i) (vote1 i))
))))

(check-sat)
;(get-model)
(pop)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(exit)

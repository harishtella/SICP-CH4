;;;;AMB EVALUATOR FROM SECTION 4.3 OF
;;;; STRUCTURE AND INTERPRETATION OF COMPUTER PROGRAMS

;;;;Matches code in ch4.scm.
;;;; To run the sample programs and exercises, code below also includes
;;;; -- enlarged primitive-procedures list
;;;; -- support for Let (as noted in footnote 56, p.428)

;;;;This file can be loaded into Scheme as a whole.
;;;;**NOTE**This file loads the metacircular evaluator of
;;;;  sections 4.1.1-4.1.4, since it uses the expression representation,
;;;;  environment representation, etc.
;;;;  You may need to change the (load ...) expression to work in your
;;;;  version of Scheme.
;;;;**WARNING: Don't load mceval twice (or you'll lose the primitives
;;;;  interface, due to renamings of apply).

;;;;Then you can initialize and start the evaluator by evaluating
;;;; the two lines at the end of the file ch4-mceval.scm
;;;; (setting up the global environment and starting the driver loop).


  


;;**implementation-dependent loading of evaluator file
;;Note: It is loaded first so that the section 4.2 definition
;; of eval overrides the definition from 4.1.1
(load "ch4-mceval.scm")



;;;Code from SECTION 4.3.3, modified as needed to run it

(define (amb? exp) (tagged-list? exp 'amb))
(define (amb-choices exp) (cdr exp))
(define (ramb? exp) (tagged-list? exp 'ramb))
(define (ramb-choices exp) (cdr exp))

;; analyze from 4.1.6, with clause from 4.3.3 added
;; and also support for Let
(define (analyze exp)
  (cond ((self-evaluating? exp) 
         (analyze-self-evaluating exp))
        ((quoted? exp) (analyze-quoted exp))
        ((variable? exp) (analyze-variable exp))
        ((assignment? exp) (analyze-assignment exp))
        ((definition? exp) (analyze-definition exp))
        ((if? exp) (analyze-if exp))
        ((lambda? exp) (analyze-lambda exp))
        ((begin? exp) (analyze-sequence (begin-actions exp)))
        ((cond? exp) (analyze (cond->if exp)))
        ((let? exp) (analyze (let->combination exp))) ;**
        ((amb? exp) (analyze-amb exp))                ;**
        ((ramb? exp) (analyze-ramb exp))                ;**
        ((application? exp) (analyze-application exp))
        (else
         (error "Unknown expression type -- ANALYZE" exp))))

(define (ambeval exp env succeed fail)
  ((analyze exp) env succeed fail))

;;;Simple expressions

(define (analyze-self-evaluating exp)
  (lambda (env succeed fail)
    (succeed exp fail)))

(define (analyze-quoted exp)
  (let ((qval (text-of-quotation exp)))
    (lambda (env succeed fail)
      (succeed qval fail))))

(define (analyze-variable exp)
  (lambda (env succeed fail)
    (succeed (lookup-variable-value exp env)
             fail)))

(define (analyze-lambda exp)
  (let ((vars (lambda-parameters exp))
        (bproc (analyze-sequence (lambda-body exp))))
    (lambda (env succeed fail)
      (succeed (make-procedure vars bproc env)
               fail))))

;;;Conditionals and sequences

(define (analyze-if exp)
  (let ((pproc (analyze (if-predicate exp)))
        (cproc (analyze (if-consequent exp)))
        (aproc (analyze (if-alternative exp))))
    (lambda (env succeed fail)
      (pproc env
             ;; success continuation for evaluating the predicate
             ;; to obtain pred-value
             (lambda (pred-value fail2)
               (if (true? pred-value)
                   (cproc env succeed fail2)
                   (aproc env succeed fail2)))
             ;; failure continuation for evaluating the predicate
             fail))))

(define (analyze-sequence exps)
  (define (sequentially a b)
    (lambda (env succeed fail)
      (a env
         ;; success continuation for calling a
         (lambda (a-value fail2)
           (b env succeed fail2))
         ;; failure continuation for calling a
         fail)))
  (define (loop first-proc rest-procs)
    (if (null? rest-procs)
        first-proc
        (loop (sequentially first-proc (car rest-procs))
              (cdr rest-procs))))
  (let ((procs (map analyze exps)))
    (if (null? procs)
        (error "Empty sequence -- ANALYZE"))
    (loop (car procs) (cdr procs))))

;;;Definitions and assignments

(define (analyze-definition exp)
  (let ((var (definition-variable exp))
        (vproc (analyze (definition-value exp))))
    (lambda (env succeed fail)
      (vproc env                        
             (lambda (val fail2)
               (define-variable! var val env)
               (succeed 'ok fail2))
             fail))))

(define (analyze-assignment exp)
  (let ((var (assignment-variable exp))
        (vproc (analyze (assignment-value exp))))
    (lambda (env succeed fail)
      (vproc env
             (lambda (val fail2)        ; *1*
               (let ((old-value
                      (lookup-variable-value var env))) 
                 (set-variable-value! var val env)
                 (succeed 'ok
                          (lambda ()    ; *2*
                            (set-variable-value! var
                                                 old-value
                                                 env)
                            (fail2)))))
             fail))))

;;;Procedure applications

(define (analyze-application exp)
  (let ((fproc (analyze (operator exp)))
        (aprocs (map analyze (operands exp))))
    (lambda (env succeed fail)
      (fproc env
             (lambda (proc fail2)
               (get-args aprocs
                         env
                         (lambda (args fail3)
                           (execute-application
                            proc args succeed fail3))
                         fail2))
             fail))))

(define (get-args aprocs env succeed fail)
  (if (null? aprocs)
      (succeed '() fail)
      ((car aprocs) env
                    ;; success continuation for this aproc
                    (lambda (arg fail2)
                      (get-args (cdr aprocs)
                                env
                                ;; success continuation for recursive
                                ;; call to get-args
                                (lambda (args fail3)
                                  (succeed (cons arg args)
                                           fail3))
                                fail2))
                    fail)))

(define (execute-application proc args succeed fail)
  (cond ((primitive-procedure? proc)
         (succeed (apply-primitive-procedure proc args)
                  fail))
        ((compound-procedure? proc)
         ((procedure-body proc)
          (extend-environment (procedure-parameters proc)
                              args
                              (procedure-environment proc))
          succeed
          fail))
        (else
         (error
          "Unknown procedure type -- EXECUTE-APPLICATION"
          proc))))

;;;amb expressions

(define (analyze-amb exp)
  (let ((cprocs (map analyze (amb-choices exp))))
    (lambda (env succeed fail)
      (define (try-next choices)
        (if (null? choices)
            (fail)
            ((car choices) env
                           succeed
                           (lambda ()
                             (try-next (cdr choices))))))
      (try-next cprocs))))

;;;Driver loop

(define input-prompt ";;; Amb-Eval input:")
(define output-prompt ";;; Amb-Eval value:")

(define (driver-loop)
  (define (internal-loop try-again)
    (prompt-for-input input-prompt)
    (let ((input (read)))
      (if (eq? input 'try-again)
          (try-again)
          (begin
            (newline)
            (display ";;; Starting a new problem ")
            (ambeval input
                     the-global-environment
                     ;; ambeval success
                     (lambda (val next-alternative)
                       (announce-output output-prompt)
                       (user-print val)
                       (internal-loop next-alternative))
                     ;; ambeval failure
                     (lambda ()
                       (announce-output
                        ";;; There are no more values of")
                       (user-print input)
                       (driver-loop)))))))
  (internal-loop
   (lambda ()
     (newline)
     (display ";;; There is no current problem")
     (driver-loop))))


;;; for interpreting code so I dont have to type it in
;;; manually at the repl

(define (interpret text)
  (define (internal-loop try-again)
    (let ((input text))
      (if (eq? input 'try-again)
          (try-again)
          (begin
            (newline)
            (display ";;; Starting a new problem ")
            (ambeval input
                     the-global-environment
                     ;; ambeval success
                     (lambda (val next-alternative)
                       (announce-output output-prompt)
                       (user-print val))
                     ;; ambeval failure
                     (lambda ()
                       (announce-output
                        ";;; There are no more values of")
                       (user-print input)))))))
  (internal-loop
   (lambda ()
     (newline)
     (display ";;; There is no current problem"))))


;;; Support for Let (as noted in footnote 56, p.428)

(define (let? exp) (tagged-list? exp 'let))
(define (let-bindings exp) (cadr exp))
(define (let-body exp) (cddr exp))

(define (let-var binding) (car binding))
(define (let-val binding) (cadr binding))

(define (make-combination operator operands) (cons operator operands))

(define (let->combination exp)
  ;;make-combination defined in earlier exercise
  (let ((bindings (let-bindings exp)))
    (make-combination (make-lambda (map let-var bindings)
                                   (let-body exp))
                      (map let-val bindings))))
                     


;; A longer list of primitives -- suitable for running everything in 4.3
;; Overrides the list in ch4-mceval.scm
;; Has Not to support Require; various stuff for code in text (including
;;  support for Prime?); integer? and sqrt for exercise code;
;;  eq? for ex. solution

(define primitive-procedures
  (list (list 'car car)
        (list 'cdr cdr)
        (list 'cadr cadr)
        (list 'cons cons)
        (list 'null? null?)
        (list 'list list)
        (list 'memq memq)
        (list 'member member)
        (list 'not not)
        (list 'and (lambda (x y) (and x y)))
		(list 'xor (lambda (x y) (and (or x y)
									  (not (and x y)))))
        (list '+ +)
        (list '- -)
        (list '* *)
        (list '= =)
        (list '> >)
        (list '< <)
        (list '>= >=)
        (list '<= <=)
        (list 'abs abs)
        (list 'remainder remainder)
        (list 'integer? integer?)
        (list 'sqrt sqrt)
        (list 'eq? eq?)
		(list 'append append)
		(list 'display display)
;;      more primitives
        ))


'AMB-EVALUATOR-LOADED

(define the-global-environment (setup-environment))

;------------------------------------------------------------------------

 
(interpret 
'(define (require p)
  (if (not p) (amb))))

#|
 
(interpret 
'(define (an-element-of items)
  (require (not (null? items)))
  (amb (car items) (an-element-of (cdr items)))))

(interpret 
'(define (an-integer-starting-from n)
  (amb n (an-integer-starting-from (+ n 1)))))

; EX. 4.35
(interpret 
'(define (an-integer-between low high)
  (require (<= low high))
  (amb low (an-integer-between (+ low 1) high))))

(interpret 
'(define (distinct? items) 
  (cond ((null? items) true) 
        ((null? (cdr items)) true) 
        ((member (car items) (cdr items)) false) 
        (else (distinct? (cdr items))))) )

(interpret 
'(define (a-pythagorean-triple-between low high)
  (let ((i (an-integer-between low high)))
	(let ((j (an-integer-between i high)))
	  (let ((k (an-integer-between j high)))
		(require (= (+ (* i i) (* j j)) (* k k)))
		(list i j k))))))


; EX. 4.36
(interpret 
'(define (all-pythag-trips)
  (let ((k (an-integer-starting-from 1)))
	(let ((j (an-integer-between 1 k)))
	  (let ((i (an-integer-between 1 j)))
		(require (= (+ (* i i) (* j j)) (* k k)))
		(list i j k))))))


; EX 4.40
(interpret
'(define (multiple-dwelling-quick) 
  (let ((baker (amb 1 2 3 4 5))) 
	(require (not (= baker 5)))
	(let ((cooper (amb 1 2 3 4 5)))
	  (require (not (= cooper 1)))
	  (let ((fletcher (amb 1 2 3 4 5)))
		(require (not (= fletcher 5)))
		(require (not (= fletcher 1)))
		(require (not (= (abs (- fletcher cooper)) 1))) 
		(let ((miller (amb 1 2 3 4 5)))
		  (require (> miller cooper))
		  (let ((smith (amb 1 2 3 4 5)))
			(require (not (= (abs (- smith fletcher)) 1))) 
			(require 
			  (distinct? (list baker cooper fletcher miller smith)))
			(list (list 'baker baker)
				  (list 'cooper cooper) 
				  (list 'fletcher fletcher) 
				  (list 'miller miller) 
				  (list 'smith smith)))))))))


; EX 4.42
(interpret
'(define (liars-puzzle)
  (let ((b (amb 1 2 3 4 5))
		(e (amb 1 2 3 4 5))
		(j (amb 1 2 3 4 5))
		(k (amb 1 2 3 4 5))
		(m (amb 1 2 3 4 5)))
	(require (distinct? (list b e j k m)))
	(require (xor (= k 2) (= b 3)))
	(require (xor (= e 1) (= j 2)))
	(require (xor (= j 3) (= e 5)))
	(require (xor (= k 2) (= m 4)))
	(require (xor (= m 4) (= b 1)))
	(list 'b b 'e e 'j j 'k k 'm m))))

; EX 4.43
; learned to see relationships from both ways to 
; get at the answer
(interpret 
'(define (fun-puzzle)
  (define (father->yacht f)
	(cond ((eq? f 'moore) 'lorna)
		  ((eq? f 'downing) 'melissa)
		  ((eq? f 'hall) 'rosalind)
		  ((eq? f 'barnacle) 'gabrielle)
		  ((eq? f 'parker) 'mary-ann)))
  (define (parker-daughter r l)
	(if (eq? r 'parker) 'rosalind 'lorna))
  (let ((lorna (amb 'downing 'hall 'parker))
		(rosalind (amb 'downing 'hall 'parker))
		(gabrielle (amb 'downing 'hall)))
	(require (distinct? (list lorna rosalind gabrielle)))
	(require (eq? (father->yacht gabrielle) (parker-daughter rosalind lorna)))
	(list 'lorna lorna))))


; EX 4.44
(interpret
'(define (eight-queens)
  (define (row q)
	(car q))
  (define (col q)
	(display "col")
	(cadr q))
  (define (col-num q)
	(let ((c (col q)))
	  (cond ((eq? q 'a) 1)
			((eq? q 'b) 2)
			((eq? q 'c) 3)
			((eq? q 'd) 4)
			((eq? q 'e) 5)
			((eq? q 'f) 6)
			((eq? q 'g) 7)
			((eq? q 'h) 8))))
  (define (on-diag q1 q2)
	(= (abs (- (row q1) (row q2)))
	   (abs (- (col-num q1) (col-num q2)))))
  (define (safe? q-pair)
	(display "safe")
	(let ((q1 (car q-pair))
		  (q2 (cadr q-pair)))
	  (and (not (eq? (row q1) (row q2)))
		   (not (eq? (col q1) (col q2)))
		   (not (on-diag q1 q2)))))
  (define (choose2 things)
	(define (c-for-one c xs)
	  (if (null? xs)
		'()
		(cons (cons c (car xs)) (c-for-one c (cdr xs)))))
	(if (null? things)
	  '()
	  (append (c-for-one (car things) (cdr things))
			  (choose2 (cdr things)))))
  (define (map f xs)
	(if (null? xs)
	  '()
	  (cons (f (car xs)) (map f (cdr xs)))))
  (define (reduce f xs)
	(if (null? (cdr xs))
	  (car xs)
	  (f (car xs) (reduce f (cdr xs)))))
  (define (safe-test q qs)
	(reduce and 
			(map safe?
				 (map (lambda (x) (list q x))
					  qs))))
  (let ((q1 (cons 'a (amb 1 2 3 4 5 6 7 8)))
		(q2 (cons 'b (amb 1 2 3 4 5 6 7 8))))
	(require (safe-test q1 (list q2)))
	(let ((q3 (cons 'c (amb 1 2 3 4 5 6 7 8))))
	  (require (safe-test q3 (list q1 q2)))
	  (let ((q4 (cons 'd (amb 1 2 3 4 5 6 7 8))))
		(require (safe-test q4 (list q1 q2 q3)))
		(let ((q5 (cons 'e (amb 1 2 3 4 5 6 7 8))))
		  (require (safe-test q5 (list q1 q2 q3 q4)))
		  (let ((q6 (cons 'f (amb 1 2 3 4 5 6 7 8))))
			(require (safe-test q6 (list q1 q2 q3 q4 q5)))
			(let ((q7 (cons 'g (amb 1 2 3 4 5 6 7 8))))
			  (require (safe-test q7 (list q1 q2 q3 q4 q5 q6)))
			  (let ((q8 (cons 'h  (amb 1 2 3 4 5 6 7 8))))
				(require (safe-test q8 (list q1 q2 q3 q4 q5 q6 q7)))
				(list q1 q2 q3 q4 q5 q6 q7 q8))))))))))

|#

;;;SECTION 4.3.2 -- Parsing natural language
(interpret '(define nouns '(nouns student professor cat class)))
(interpret '(define verbs '(verbs studies lectures eats sleeps)))
(interpret '(define articles '(articles the a)))
(interpret '(define prepositions '(preps for to in by with)))
(interpret '(define adverbs '(adverbs poorly boringly sloppily)))
(interpret '(define adjectives '(adjectives smart dirty lazy brilliant)))


(interpret 
'(define (parse-word word-list)
  (require (not (null? *unparsed*)))
  (require (memq (car *unparsed*) (cdr word-list)))
  (let ((found-word (car *unparsed*)))
    (set! *unparsed* (cdr *unparsed*))
    (list (car word-list) found-word))))


(interpret '(define *unparsed* '()))

(interpret 
'(define (parse input)
  (set! *unparsed* input)
  (let ((sent (parse-sentence)))
    (require (null? *unparsed*))
    sent)))

(interpret 
'(define (parse-prepositional-phrase)
  (list 'prep-phrase
        (parse-word prepositions)
        (parse-noun-phrase-x))))

(interpret 
'(define (parse-sentence)
  (list 'sentence
         (parse-noun-phrase-x)
         (parse-verb-phrase-x))))

(interpret 
'(define (parse-verb-phrase)
  (define (maybe-extend verb-phrase)
    (amb verb-phrase
         (maybe-extend (list 'verb-phrase
                             verb-phrase
                             (parse-prepositional-phrase)))))
  (maybe-extend (parse-word verbs))))

(interpret 
'(define (parse-simple-noun-phrase)
  (list 'simple-noun-phrase
        (parse-word articles)
        (parse-word nouns))))

(interpret 
'(define (parse-noun-phrase)
  (define (maybe-extend noun-phrase)
    (amb noun-phrase
         (maybe-extend (list 'noun-phrase
                             noun-phrase
                             (parse-prepositional-phrase)))))
  (maybe-extend (parse-simple-noun-phrase))))

; EX 4.48
(interpret 
'(define (parse-verb-phrase-x)
  (define (maybe-extend verb-phrase)
    (amb verb-phrase
         (maybe-extend (list 'verb-phrase
                             verb-phrase
                             (amb (parse-word adverbs) 
								  (parse-prepositional-phrase))))))
  (maybe-extend (parse-word verbs))))

(interpret 
'(define (parse-noun-phrase-x)
; Unlike the code for EX 4.47, noun-phrase-with-adjs does not ever go into an infinite 
; loop. This parses an adjective before doing a recursive call. If it cant parse an
; adjective the recursive call is not made. 
;
; This method works here because we are looking for adjectives 
; before the noun. In EX 4.47 it is searching for prep phrases after a verb.
; It was searching for that initializing verb on each recursive call. 
; When you do try-again until it goes to the other branch of the amb that doesn't
; capture that initializing verb it goes off into an infinite loop. 
  (define (noun-phrase-with-adjs)
	(amb (parse-word nouns)
		 (list 'noun-phrase 
			   (parse-word adjectives)
			   (noun-phrase-with-adjs))))
  (define (noun-phrase-with-adjs-and-article)
	(list 'noun-phrase 
		  (parse-word articles)
		  (noun-phrase-with-adjs)))
  (define (maybe-prep noun-phrase)
    (amb noun-phrase
         (maybe-prep (list 'noun-phrase
                             noun-phrase
							 (parse-prepositional-phrase)))))
  (maybe-prep (amb (noun-phrase-with-adjs)
				   (noun-phrase-with-adjs-and-article)))))
  

;; EXERCISE 4.47
;; this is trying to match more and more prepositional phrases going leftwards,
;; it will go into an infinite loop if you 'try again' after it returns a result with
;; the max available prep phrases describing the verb.
;;
;; the order does matter, if the two amb args were swapped we would immediately
;; get an infinite loop.
;;
;; the original parse-verb-phrase is going rightwards and knows when it has run
;; out of tokens to match
'(define (parse-verb-phrase)
  (amb (parse-word verbs)
       (list 'verb-phrase
             (parse-verb-phrase)
             (parse-prepositional-phrase))))

; EX 4.49
(interpret 
'(define (parse-word word-list)
   (let ((w (choose-one (cdr word-list)))
		 (l (list->name word-list)))
	 (set! l (remove w word-list))
	 (list (car word-list) w))))

(interpret 
'(define (list->name l)
   (car l)))

; returns a list like xs with first instance of y removed
(interpret
'(define (remove y xs)
  (define (remove-h y xp xs)
	(if (null? xs)
	  xp
	  (if (eq? y (car xs)) 
		(append xp (cdr xs))
		(remove-h y 
				  (append xp (list (car xs))) 
				  (cdr xs)))))
  (remove-h y '() xs)))

(interpret
'(define (choose-one xs)
   (require (not (null? xs)))
   (amb (car xs)
		(choose-one (cdr xs)))))

(interpret 
'(define (gen)
   (parse-sentence)))

; EX 4.50
(define (analyze-ramb exp)
  (define (remove y xs)
	(define (remove-h y xp xs)
	  (if (null? xs)
		xp
		(if (eq? y (car xs)) 
		  (append xp (cdr xs))
		  (remove-h y 
					(append xp (list (car xs))) 
					(cdr xs)))))
	(remove-h y '() xs))

  (define (random-elem lst)
	(define (nth i lst)
	  (if (eq? i 0)
		(car lst)
		(nth (- i 1) (cdr lst))))
	(nth (random (length lst)) lst))

  (let ((cprocs (map analyze (amb-choices exp))))
    (lambda (env succeed fail)
      (define (try-next choices)
        (if (null? choices)
            (fail)
			(let ((rc (random-elem choices)))
			  (rc env
				  succeed
				  (lambda ()
					(try-next (remove rc choices)))))))
	  (try-next cprocs))))

;; Startup repl on file load
(driver-loop)


;;;;METACIRCULAR EVALUATOR FROM CHAPTER 4 (SECTIONS 4.1.1-4.1.4) of
;;;; STRUCTURE AND INTERPRETATION OF COMPUTER PROGRAMS

;;;;Matches code in ch4.scm

;;;;This file can be loaded into Scheme as a whole.
;;;;Then you can initialize and start the evaluator by evaluating
;;;; the two commented-out lines at the end of the file (setting up the
;;;; global environment and starting the driver loop).

;;;;**WARNING: Don't load this file twice (or you'll lose the primitives
;;;;  interface, due to renamings of apply).

;;;from section 4.1.4 -- must precede def of metacircular apply
(define apply-in-underlying-scheme apply)

;;;SECTION 4.1.1

(define (eval exp env)
  (cond ((self-evaluating? exp) exp)
        ((variable? exp) (lookup-variable-value exp env))
        ((quoted? exp) (text-of-quotation exp))
        ((assignment? exp) (eval-assignment exp env))
        ((definition? exp) (eval-definition exp env))
        ((if? exp) (eval-if exp env))
        ((lambda? exp)
         (make-procedure (lambda-parameters exp)
                         (lambda-body exp)
                         env))
        ((begin? exp) 
         (eval-sequence (begin-actions exp) env))
        ((cond? exp) (eval (cond->if exp) env))
		((and? exp) (eval-and (preds exp) env))
		((or? exp) (eval-or (preds exp) env))
		((let? exp) (eval (let->combination exp) env))
		((let*? exp) (eval (let*->nested-lets exp) env))
		((letrec? exp) (eval (letrec->let exp) env))
		((while? exp) (eval (while->combination exp) env))
		((for? exp) (eval-for exp env))
        ((application? exp)
         (apply (eval (operator exp) env)
                (list-of-values (operands exp) env)))
        (else
         (error "Unknown expression type -- EVAL" exp))))

(define (apply procedure arguments)
  (cond ((primitive-procedure? procedure)
         (apply-primitive-procedure procedure arguments))
        ((compound-procedure? procedure)
         (eval-sequence
           (procedure-body procedure)
           (extend-environment
             (procedure-parameters procedure)
             arguments
             (procedure-environment procedure))))
        (else
         (error
          "Unknown procedure type -- APPLY" procedure))))

;-----

(define (letrec? exp) (tagged-list? exp 'letrec))

(define (letrec-binds exp) (cadr exp))
(define (letrec-bind-names exp) (map car (cadr exp)))
(define (letrec-make-set bind-pair) (list 'set! (car bind-pair) (cadr bind-pair)))
(define (letrec-body exp) (cddr exp))

(define (letrec->let exp)
  (let ((binds-init (map (lambda (x) (list x ''*unassigned*))
						 (letrec-bind-names exp)))
		(binds-sets (map letrec-make-set (letrec-binds exp)))) 
	(make-let binds-init (append binds-sets (letrec-body exp)))))   


;-----

;(define foo (lambda (x y)  
;                 (define (bar x) (* 3 x))
;				 (define pp (+ 3 2))
;                 (define (baz z) (* 8 z))
;                 (+ (bar x) (baz y) pp)
;                 ))

;(foo 2 3)


(define (scan-out-defines exp)
  (define (make-set d)
	(list 'set! (definition-variable d) (definition-value d))) 
  (define (make-body-wod defines other)
	  (if (null? defines)
		other
		(list
		  (make-let 
			(map (lambda (x) (list x ''*unassigned*)) 
				 (map definition-variable defines)) 
			(sequence->exp
			  (append
				(map make-set defines)
				other))))))
  (define (sod-h exp-s defines other)
	(if (null? exp-s)
	  (make-body-wod 
		(reverse defines)
		(reverse other))
	  (let ((e (car exp-s)))
		(if (definition? e)
		  (sod-h (cdr exp-s) 
				 (cons e defines)
				 other)
		  (sod-h (cdr exp-s)
				 defines
				 (cons e other))))))
  (sod-h exp '() '()))


;-----
(define (for? exp)
  (tagged-list? exp 'for))

(define (for-init-vars exp) (map car (cadr exp)))
(define (for-init-exps exp) (map cadr (cadr exp)))
(define (for-test exp) (caddr exp))
(define (for-next-op exp) (cadddr exp))
(define (for-body exp) (cadddr (cdr exp)))

(define (eval-for exp env)
  (make-begin
	(list
	  (make-define 
		(cons 'loop (for-init-vars exp)) 
		(list (make-if (for-test exp)
					   (make-begin
						 (list
						   (for-body exp)
						   (for-next-op exp)
						   (cons 'loop (for-init-vars exp))))
					   'nil)))
	  (cons 'loop (for-init-exps exp)))))

;(for ((a 3)(b 6)) (< a 10) (set! a (+ a 1)) (set! b (* b 2)))
;(define (loop (init exp)) (begin (for-body for-next-op) (if for-test loop vars) 

(define (while-body exp) (caddr exp))
(define (while-cond exp) (cadr exp))

(define (while? exp)
  (tagged-list? exp 'while))

(define (eval-while exp env)
  (if (true? (eval (while-cond exp) env))
	(begin
	  (eval (while-body exp) env)
	  (eval exp env))))

; better way to do while
(define (while->combination exp)
  (make-if (while-cond exp) 
		   (sequence->exp 
			 (list
			   (while-body exp)
			   exp))
		   '()))

;-----

(define (let*? exp)
  (tagged-list? exp 'let*))

(define (let*->nested-lets exp)
  (let ((binds (let*-binds exp)))
	(make-let (list (car binds)) 
			  (let*-h (cdr binds) (let*-body exp)))))

(define (let*-h bindings body)
  (if (pair? bindings) 
	(list (make-let (list (car bindings)) (let*-h (cdr bindings) body)))
	body))

(define (make-let bindings body)
  (cons 'let (cons bindings body)))

(define (let*-binds exp) (cadr exp))
(define (let*-body exp) (cddr exp))


;-----

(define (let? exp) 
  (tagged-list? exp 'let))

(define (named-let? exp)
  (symbol? (cadr exp)))

(define (let-name exp) (cadr exp))
(define (let-named-exps exp) (map cadr (caddr exp)))
(define (let-named-vars exp) (map car (caddr exp)))
(define (let-named-body exp) (cadddr exp))

(define (let->combination exp) 
  (if (named-let? exp)
	(make-begin
	  (list
		(make-define 
		  (cons (let-name exp) (let-named-vars exp))
		  (list (let-named-body exp)))
		(cons (let-name exp) (let-named-exps exp))))
	(cons (make-lambda (let-vars exp)
					   (let-body exp))
		  (let-exps exp))))

(define (let-vars exp) (map car (cadr exp)))
(define (let-exps exp) (map cadr (cadr exp)))
(define (let-body exp) (cddr exp))

;-----

(define (and? exp)
  (tagged-list? exp 'and))

(define (or? exp)
  (tagged-list? exp 'or))

;could have done these more simply but its OK
(define (eval-and exp env)
  (define (eval-and-h exp env last)
    (if (not (null? exp))
        (let ((pred-res (eval (first-pred exp) env)))
          (if (false? pred-res)
              false
              (eval-and-h (rest-of-preds exp) env pred-res)))
        last))
  (eval-and-h exp env true))
        
          
(define (eval-or exp env)
  (if (not (null? exp))
	(let ((pred-res (eval (first-pred exp) env)))
	  (if (true? pred-res)
		pred-res
		(eval-or (rest-of-preds exp) env)))
	false))

(define (preds exp)
  (cdr exp))
(define (first-pred exp)
  (car exp))
(define (rest-of-preds exp)
  (cdr exp))

(define (list-of-values exps env)
  (if (no-operands? exps)
      '()
      (cons (eval (first-operand exps) env)
            (list-of-values (rest-operands exps) env))))

(define (eval-if exp env)
  (if (true? (eval (if-predicate exp) env))
      (eval (if-consequent exp) env)
      (eval (if-alternative exp) env)))

(define (eval-sequence exps env)
  (cond ((last-exp? exps) (eval (first-exp exps) env))
        (else (eval (first-exp exps) env)
              (eval-sequence (rest-exps exps) env))))

(define (eval-assignment exp env)
  (set-variable-value! (assignment-variable exp)
                       (eval (assignment-value exp) env)
                       env)
  'ok)

(define (eval-assignment2 exp env)
  (eval-definition2 exp env))

(define (eval-definition exp env)
  (define-variable! (definition-variable exp)
                    (eval (definition-value exp) env)
                    env)
  'ok)

(define (eval-definition2 exp env)
   (define-variable! (definition-variable2 exp)
                    (eval (definition-value2 exp) env)
                    env)
  'ok)




;;;SECTION 4.1.2

(define (self-evaluating? exp)
  (cond ((number? exp) true)
        ((string? exp) true)
        (else false)))

(define (quoted? exp)
  (tagged-list? exp 'quote))

(define (text-of-quotation exp) (cadr exp))

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      false))

(define (variable? exp) (symbol? exp))

(define (assignment? exp)
  (tagged-list? exp 'set!))

(define (assignment2? exp)
  (eq? (cadr exp) '=))

(define (assignment-variable exp) (cadr exp))

(define (assignment-value exp) (caddr exp))

(define (make-define name-params body)
  (cons 'define (cons name-params body)))

(define (definition? exp)
  (tagged-list? exp 'define))

(define (definition2? exp)
  (eq? (cadr exp) '=))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (cddr exp))))

(define (definition-variable2 exp)
  (if (symbol? (car exp))
      (car exp)
      (caar exp)))

(define (definition-value2 exp)
  (if (symbol? (car exp))
      (caddr exp)
      (make-lambda (cdar exp)
                   (cddr exp))))

(define (lambda? exp) (tagged-list? exp 'lambda))

(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

(define (make-lambda parameters body)
  (cons 'lambda (cons parameters body)))


(define (if? exp) (tagged-list? exp 'if))

(define (if-predicate exp) (cadr exp))

(define (if-consequent exp) (caddr exp))

(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      'false))

(define (make-if predicate consequent alternative)
  (list 'if predicate consequent alternative))


(define (begin? exp) (tagged-list? exp 'begin))

(define (begin-actions exp) (cdr exp))

(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))

(define (sequence->exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq) (cons 'begin seq))


(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))

(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))


(define (cond? exp) (tagged-list? exp 'cond))

(define (cond-clauses exp) (cdr exp))

(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) 'else))

(define (cond-predicate clause) (car clause))

(define (cond-actions clause) (cdr clause))

(define (cond->if exp)
  (expand-clauses (cond-clauses exp)))

; ex 4.5
(define (cond-ex-clause? exp) (eq? (cadr exp) '=>))
(define (cond-ex-action exp) (caddr exp))

(define (expand-clauses clauses)
  (if (null? clauses)
      'false                          ; no else clause
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (cond 
          ((cond-else-clause? first)
          (if (null? rest)
                (sequence->exp (cond-actions first))
                (error "ELSE clause isn't last -- COND->IF"
                       clauses)))
; ex 4.5
          ((cond-ex-clause? first) 
           (let ((cp (cond-predicate first)))
              (make-if cp
                     (list (cond-ex-action first) cp)
                     (expand-clauses rest)))) 
          (else
           (make-if (cond-predicate first)
                    (sequence->exp (cond-actions first))
                    (expand-clauses rest)))))))

;;;SECTION 4.1.3

(define (true? x)
  (not (eq? x false)))

(define (false? x)
  (eq? x false))


(define (make-procedure parameters body env)
  (let ((body-wo-defs (scan-out-defines body)))
	(list 'procedure parameters body-wo-defs env)))

(define (compound-procedure? p)
  (tagged-list? p 'procedure))


(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))


(define (enclosing-environment env) (cdr env))

(define (first-frame env) (car env))

(define the-empty-environment '())

(define (make-frame variables values)
  (cons variables values))

(define (frame-variables frame) (car frame))
(define (frame-values frame) (cdr frame))

(define (add-binding-to-frame! var val frame)
  (set-car! frame (cons var (car frame)))
  (set-cdr! frame (cons val (cdr frame))))

(define (extend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (cons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error "Too many arguments supplied" vars vals)
          (error "Too few arguments supplied" vars vals))))

;----
; XXX figure out how to do multiline comments for 
; next 3 func
(define (lookup-variable-value var env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (car vals))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

(define (set-variable-value! var val env)
  (define (env-loop env)
    (define (scan vars vals)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (if (eq? env the-empty-environment)
        (error "Unbound variable -- SET!" var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
  (env-loop env))

(define (define-variable! var val env)
  (let ((frame (first-frame env)))
    (define (scan vars vals)
      (cond ((null? vars)
             (add-binding-to-frame! var val frame))
            ((eq? var (car vars))
             (set-car! vals val))
            (else (scan (cdr vars) (cdr vals)))))
    (scan (frame-variables frame)
          (frame-values frame))))

;---

(define (search-frame frame var) 
  (let ((vars (frame-variables frame)) 
		(vals (frame-values frame)))
	(cond ((null? vars) nil)
		  ((eq? var (car vars)) vals)
		  (else (search-frame (cons (cdr vars) (cdr vals)) var)))))

(define (search-envs env var)
  (if (eq? env the-empty-environment)
	nil
	(let ((frame (first-frame env)))
	  (let ((res (search-frame frame var)))
		(if (null? res)
		  (search-envs (enclosing-environment env) var)
		  res)))))

(define (lookup-variable-value var env)
  (let ((res (search-envs env var)))
	(if (null? res)
	  (error "Unbound variable --" var)
	  (if (eq? (car res) '*unassigned*)
		(error "Unassiged variable --" var)
		(car res)))))

(define (set-variable! var val env)
  (let ((res (search-envs env var)))
	(if (null? res)
	  (error "Unbound variable -- SET!" var)
	  (set-car! res val))))

(define (define-variable! var val env)
  (let ((res (search-frame (first-frame env) var)))
	(if (null? res)
	  (add-binding-to-frame! var val (first-frame env))
	  (set-car! res val))))

;-----

;;;SECTION 4.1.4

(define (setup-environment)
  (let ((initial-env
         (extend-environment (primitive-procedure-names)
                             (primitive-procedure-objects)
                             the-empty-environment)))
    (define-variable! 'true true initial-env)
    (define-variable! 'false false initial-env)
    initial-env))

;[do later] (define the-global-environment (setup-environment))

(define (primitive-procedure? proc)
  (tagged-list? proc 'primitive))

(define (primitive-implementation proc) (cadr proc))

(define primitive-procedures
  (list (list 'car car)
        (list 'cdr cdr)
        (list 'cons cons)
        (list 'null? null?)
        (list '+ +)
        (list '- -)
        (list '* *)
        (list '/ /)
        (list '> >)
        (list '>= >=)
        (list '< <)
        (list '<= <=)
        (list '= =)
        (list 'display display)
;;      more primitives
        ))

(define (primitive-procedure-names)
  (map car
       primitive-procedures))

(define (primitive-procedure-objects)
  (map (lambda (proc) (list 'primitive (cadr proc)))
       primitive-procedures))

;[moved to start of file] (define apply-in-underlying-scheme apply)

(define (apply-primitive-procedure proc args)
  (apply-in-underlying-scheme
   (primitive-implementation proc) args))



(define input-prompt ";;; M-Eval input:")
(define output-prompt ";;; M-Eval value:")

(define (driver-loop)
  (prompt-for-input input-prompt)
  (let ((input (read)))
    (let ((output (eval input the-global-environment)))
      (announce-output output-prompt)
      (user-print output)))
  (driver-loop))

(define (prompt-for-input string)
  (newline) (newline) (display string) (newline))

(define (announce-output string)
  (newline) (display string) (newline))

(define (user-print object)
  (if (compound-procedure? object)
      (display (list 'compound-procedure
                     (procedure-parameters object)
                     (procedure-body object)
                     '<procedure-env>))
      (display object)))

;;;Following are commented out so as not to be evaluated when
;;; the file is loaded.
(define the-global-environment (setup-environment))
(define tge the-global-environment)
(driver-loop)

'METACIRCULAR-EVALUATOR-LOADED

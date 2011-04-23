
; EX 4.41
(define (reduce fn lis) 
  (if (eq? (cdr lis) nil)
	(car lis)
	(fn (car lis) (reduce fn (cdr lis)))))

(define (distinct? items) 
  (cond ((null? items) true) 
        ((null? (cdr items)) true) 
        ((member (car items) (cdr items)) false) 
        (else (distinct? (cdr items))))) 

(define (multiple-dwelling-normal-scheme)
	(define assignments '())
	(define (test-assignment assgn)  
	  (display assgn)
	  (reduce (lambda (x y) (and x y)) 
			  (map (lambda (test) 
					 (let ((a (car assgn))
						   (b (cadr assgn))
						   (c (caddr assgn))
						   (d (cadddr assgn))
						   (e (car (cddddr assgn))))
					   (test a b c d e))) 
				   tests)))
	(define (test-loop assignments)
	  (if (eq? assignments nil)
		nil
		(if (eq? true (test-assignment (car assignments)))
		  (car assignments)
		  (test-loop (cdr assignments)))))
	(define tests (list
					(lambda (a b c d e) (not (= 5 a)))
					(lambda (a b c d e) (not (= 1 b)))
					(lambda (a b c d e) (not (= 5 c)))
					(lambda (a b c d e) (not (= 1 c)))
					(lambda (a b c d e) (not (= 1 (abs (- b c)))))
					(lambda (a b c d e) (> d b))
					(lambda (a b c d e) (not (= 1 (abs (- e c)))))
					(lambda (a b c d e) (distinct? (list a b c d e)))))
	(do ([a 1 (+ a 1)])
	  [(> a 5)]
	  (do ([b 1 (+ b 1)])
		[(> b 5)]
		(do ([c 1 (+ c 1)])
		  [(> c 5)]
		  (do ([d 1 (+ d 1)])
			[(> d 5)]
			(do ([e 1 (+ e 1)])
			  [(> e 5)]
			  (set! assignments (cons (list a b c d e) assignments)))))))
	(set! assignments (reverse assignments))
	(test-loop assignments))
	  
(multiple-dwelling-normal-scheme) 


#|
	
(define (loop name val body)
  (let ((name val))
	(if (<= name 5)
	  (body)
	  (loop (+ name 1)))))

(loop 'a 1 
	  (lambda () (loop 'b 1 
					   (lambda () (loop 'c 1
										(lambda () (set! assignments (cons (list a b c) 
																	assignments))))))))
(loop (a 1)
	  (if (<= a 5)
		(loop (b 1)
			  (if (<= b 5)
				(loop (c 1)
					  (if (<= c 5)
						(set! temp (cons (list a b c) temp))
						(recur (+ c 1))))
				(recur (+ b 1))))
		(recur (+ a 1))))

|#

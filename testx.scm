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
         (map (lambda (x) (eval x env))  (begin-actions exp)))
        ((cond? exp) (eval (cond-if exp) env))
        ((application? exp)
         (apply (eval (operator exp) env)
                (list-of-values (operands exp) env)))
        (else
         (error exp))))

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
          procedure))))

(define (list-of-values exps env)
  (if (no-operands? exps)
      nil
      (cons (eval (first-operand exps) env)
            (list-of-values (rest-operands exps) env))))

(define (eval-if exp env)
  (if (true? (eval (if-predicate exp) env))
      (eval (if-consequent exp) env)
      (eval (if-alternative exp) env)))

(define (eval-assignment exp env)
  (begin
    (set-variable-value (assignment-variable exp)
                       (eval (assignment-value exp) env)
                       env)
  (quote ok)))

(define (eval-definition exp env)
  (begin
    (define-variable (definition-variable exp)
                    (eval (definition-value exp) env)
                    env)
  (quote ok)))

(define (self-evaluating? exp)
  (cond ((number? exp) true)
        ((string? exp) true)
        (else false)))

(define (quoted? exp)
  (tagged-list? exp (quote quote)))

(define (text-of-quotation exp) (cadr exp))

(define (tagged-list? exp tag)
  (if (pair? exp)
      (eq? (car exp) tag)
      false))

(define (definition-variable exp)
  (if (symbol? (cadr exp))
      (cadr exp)
      (caadr exp)))

(define (definition-value exp)
  (if (symbol? (cadr exp))
      (caddr exp)
      (make-lambda (cdadr exp)
                   (cddr exp))))

(define (lambda? exp)
  (tagged-list? exp (quote lambda)))

(define (definition? exp)
  (tagged-list? exp (quote define)))


(define (lambda-parameters exp) (cadr exp))
(define (lambda-body exp) (cddr exp))

(define (make-lambda parameters body)
  (cons (quote lambda) (cons parameters body)))


(define (if? exp) (tagged-list? exp (quote if)))

(define (if-predicate exp) (cadr exp))

(define (if-consequent exp) (caddr exp))

(define (if-alternative exp)
  (if (not (null? (cdddr exp)))
      (cadddr exp)
      (quote false)))

(define (make-if predicate consequent alternative)
  (list (quote if) predicate consequent alternative))


(define (begin? exp) (tagged-list? exp (quote begin)))
(define (begin-actions exp) (cdr exp))

(define (last-exp? seq) (null? (cdr seq)))
(define (first-exp seq) (car seq))
(define (rest-exps seq) (cdr seq))

(define (sequence-exp seq)
  (cond ((null? seq) seq)
        ((last-exp? seq) (first-exp seq))
        (else (make-begin seq))))

(define (make-begin seq) (cons (quote begin) seq))


(define (application? exp) (pair? exp))
(define (operator exp) (car exp))
(define (operands exp) (cdr exp))

(define (no-operands? ops) (null? ops))
(define (first-operand ops) (car ops))
(define (rest-operands ops) (cdr ops))

(define (cond? exp) (tagged-list? exp (quote cond)))

(define (cond-clauses exp) (cdr exp))

(define (cond-else-clause? clause)
  (eq? (cond-predicate clause) (quote else)))

(define (cond-predicate clause) (car clause))

(define (cond-actions clause) (cdr clause))

(define (cond-if exp)
  (expand-clauses (cond-clauses exp)))

(define (expand-clauses clauses)
  (if (null? clauses)
      (quote false)
      (let ((first (car clauses))
            (rest (cdr clauses)))
        (if (cond-else-clause? first)
            (if (null? rest)
                (sequence-exp (cond-actions first))
                (error 
                       clauses))
            (make-if (cond-predicate first)
                     (sequence-exp (cond-actions first))
                     (expand-clauses rest))))))



(define (true? x)
  (not (eq? x false)))

(define (false? x)
  (eq? x false))


(define (make-procedure parameters body env)
  (list (quote procedure) parameters body env))

(define (compound-procedure? p)
  (tagged-list? p (quote procedure)))


(define (procedure-parameters p) (cadr p))
(define (procedure-body p) (caddr p))
(define (procedure-environment p) (cadddr p))


(define (enclosing-environment env) (cdr env))

(define (first-frame env) (car env))

(define the-empty-environment nil)

(define (make-frame variables values)
  (cons variables values))

(define (frame-variables frame) (car frame))
(define (frame-values frame) (cdr frame))

(define (add-binding-to-frame var val frame)
  (begin
    (set-car frame (cons var (car frame)))
    (set-cdr frame (cons val (cdr frame)))))

(define (extend-environment vars vals base-env)
  (if (= (length vars) (length vals))
      (cons (make-frame vars vals) base-env)
      (if (< (length vars) (length vals))
          (error vars vals)
          (error vars vals))))


(define (scan vars vals env)
      (cond ((null? vars)
             (env-loop (enclosing-environment env)))
            ((eq? var (car vars))
             (car vals))
            (else (scan (cdr vars) (cdr vals)))))

(define (env-loop var env)
  (if (eq? env the-empty-environment)
        (error var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame) env))))

(define (lookup-variable-value var env)
  (env-loop var env))

(define (scan-set vars vals env)
  (cond ((null? vars)
         (env-loop-set (enclosing-environment env)))
        ((eq? var (car vars))
         (set-car vals val))
        (else (scan-set (cdr vars) (cdr vals)))))

(define (env-loop-set var val env)
  (if (eq? env the-empty-environment)
        (error var)
        (let ((frame (first-frame env)))
          (scan (frame-variables frame)
                (frame-values frame)))))
    
(define (set-variable-value var val env)
 
  (env-loop-set var val  env))

(define (scan-define vars vals frame)
      (cond ((null? vars)
             (add-binding-to-frame var val frame))
            ((eq? var (car vars))
             (set-car vals val))
            (else (scan-define (cdr vars) (cdr vals) frame))))

(define (define-variable var val env)
  (let ((frame (first-frame env)))
    (scan-define
     (frame-variables frame)
      (frame-values frame))))

(define (setup-environment dummy)
  (let ((initial-env
         (extend-environment (primitive-procedure-names dummy)
                             (primitive-procedure-objects dummy)
                             the-empty-environment)))
    (begin
      (define-variable (quote true)true initial-env)
      (define-variable (quote false) false initial-env)
      initial-env)))

(define (primitive-procedure? proc)
  (tagged-list? proc (quote primitive)))

(define (primitive-implementation proc) (cadr proc))

(define primitive-procedures
  (list (list (quote car) car)
        (list (quote cdr) cdr)
        (list (quote cons) cons)
        (list (quote null?) null?)
        ))

(define (primitive-procedure-names dummy)
  (map car
       primitive-procedures))

(define (primitive-procedure-objects dummy)
  (map (lambda (proc) (list (quote primitive) (cadr proc)))
       primitive-procedures))

(define (apply-primitive-procedure proc args)
  (apply-in-underlying-scheme
   (primitive-implementation proc) args))

(define (driver-loop dummy)
  (begin
    (let ((input (read dummy)))
      (let ((output (eval input the-global-environment)))
	(announce-output output-prompt)))
    (driver-loop dummy)))

(define (announce-output string)
  (display string))

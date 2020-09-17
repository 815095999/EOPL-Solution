#lang eopl
; ------------------------------------------------------------------------------
; Storage

; empty-store: () -> sto
(define empty-store
  (lambda () '()))

(define the-store 'uninitialized)

; get-store: () -> sto
(define get-store
  (lambda () the-store))

; initialize-store!: () -> unspecified
(define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))

; reference?: schemeval -> bool
(define reference?
  (lambda (x) (integer? x)))

; newref: expval -> ref
(define newref
  (lambda (val)
    (let ((next-ref (length the-store)))
      (set! the-store (append the-store (list val)))
      next-ref)))

; deref: ref -> expval
(define deref
  (lambda (ref)
    (list-ref the-store ref)))

; setref!: ref x expval -> unspecified
(define setref!
  (lambda (ref val)
    (letrec ((setref-inner
              (lambda (store1 ref1)
                (cond ((null? store1)
                       (report-invalid-reference ref the-store))
                      ((zero? ref1)
                       (cons val (cdr store1)))
                      (else (cons (car store1)
                                  (setref-inner (cdr store1) (- ref1 1))))))))
      (set! the-store (setref-inner the-store ref)))))

(define report-invalid-reference
  (lambda (ref store1)
    (eopl:error "invalid reference! ~s ~s" ref store1)))

; ------------------------------------------------------------------------------
; Environments
(define identifier?
  (lambda (x)
    (and (symbol? x)
         (not (equal? x 'lambda)))))
(define-datatype environment environment?
  (empty-env)
  (extend-env (var identifier?)
              (val reference?)
              (env environment?))
  (extend-env-rec (p-names (list-of identifier?))
                  (vectors (list-of vector?)) (env environment?)))

; (b-vars (list-of (list-of identifier?)))
; (bodys (list-of expression?))
(define extend-env-rec*
  (lambda (p-names b-vars bodys env)
    (define (generate-vec num)
      (if (= num 0)
          '()
          (cons (make-vector 1) (generate-vec (- num 1)))))
    (define vecs (generate-vec (length p-names)))
    (define new-env (extend-env-rec p-names vecs env))
    (define (modify-vec vecs b-vars bodys env num)
      (if (null? b-vars)
          env
          (begin (vector-set! (list-ref vecs num) 0
                              (newref (proc-val (procedure (car b-vars) (car bodys) env))))
                 (modify-vec vecs (cdr b-vars) (cdr bodys) env (+ num 1)))))
    (modify-vec vecs b-vars bodys new-env 0)))
(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
                 (report-no-binding-found search-var))
      (extend-env (saved-var saved-val saved-env)
                  (if (equal? saved-var search-var)
                      saved-val
                      (apply-env saved-env search-var)))
      (extend-env-rec (p-names vecs saved-env)
                      (if (memq search-var p-names)
                          (extract-procedure p-names vecs search-var 0)
                          (apply-env saved-env search-var))))))
(define extract-procedure
  (lambda (p-names vecs search-var num)
    (if (equal? search-var (car p-names))
        (vector-ref (list-ref vecs num) 0)
        (extract-procedure (cdr p-names) vecs search-var (+ num 1)))))
(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-env "No binding for ~s" search-var)))

(define init-env
  (lambda ()
    (extend-env 'i (newref (num-val 1))
      (extend-env 'v (newref (num-val 5))
        (extend-env 'x (newref (num-val 10))
          (empty-env))))))
; ------------------------------------------------------------------------------
; Scanner and parser specification

(define scanner-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)))

(define grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" expression) "in" expression) letrec-exp)
    (expression ("proc" "(" (separated-list identifier ",") ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("set" identifier "=" expression) assign-exp)
    (expression ("begin" expression (arbno ";" expression) "end") begin-exp)
    (expression ("pair" "(" expression "," expression ")") newpair-exp)
    (expression ("left" "(" expression ")") left-exp)
    (expression ("right" "(" expression ")") right-exp)
    (expression ("setleft" "(" expression "," expression ")") setleft-exp)
    (expression ("setright" "(" expression "," expression ")") setright-exp)
    (expression ("ref" identifier) ref-exp)
    (expression ("setref" "(" expression "," expression ")") setref-exp)
    (expression ("deref" "(" expression ")") deref-exp)
    ))
 
(sllgen:make-define-datatypes scanner-spec grammar)

; ------------------------------------------------------------------------------
; Debugging helpers for scanner and parser

(define list-the-datatypes
  (lambda()
    (sllgen:list-define-datatypes scanner-spec grammar)))

(define just-scan
  (sllgen:make-string-scanner scanner-spec grammar))

(define scan&parse
  (sllgen:make-string-parser scanner-spec grammar))

; ------------------------------------------------------------------------------
; Mutable Pair
(define-datatype mutpair mutpair?
  (a-pair (left-loc reference?)
          (right-loc reference?)))
; make-pair: expval x expval -> mutpair
(define make-pair
  (lambda (val1 val2)
    (a-pair (newref val1)
            (newref val2))))

;left: mutpair -> expval
(define left
  (lambda (p)
    (cases mutpair p
      (a-pair (le ri)
              (deref le)))))
;right: mutpair -> expval
(define right
  (lambda (p)
    (cases mutpair p
      (a-pair (le ri)
              (deref ri)))))
;setleft: mutpair x expval -> unspecified
(define setleft
  (lambda (p val)
    (cases mutpair p
      (a-pair (le ri)
              (setref! le val)))))

;setright: mutpair x expval -> unspecified
(define setright
  (lambda (p val)
    (cases mutpair p
      (a-pair (le ri)
              (setref! ri val)))))


; ------------------------------------------------------------------------------
; Expressed values
(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc proc?))
  (pair-val (pair mutpair?))
  (ref-val (ref reference?)))

; expval->ref: expval -> reference
(define expval->ref
  (lambda (val)
    (cases expval val
      (ref-val (ref) ref)
      (else (report-expval-extractor-error 'ref-val val)))))
; expval->pair: expval -> pair
(define expval->pair
  (lambda (val)
    (cases expval val
      (pair-val (pair) pair)
      (else (report-expval-extractor-error 'mutpair val)))))
; expval->num: expval -> num
(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (report-expval-extractor-error 'num val)))))
(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (report-expval-extractor-error 'bool val)))))
; expval->proc: expval -> proc
(define expval->proc
  (lambda (val)
    (cases expval val
      (proc-val (proc1) proc1)
      (else (report-expval-extractor-error 'proc-val val)))))
(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))

; ------------------------------------------------------------------------------
; proc
(define-datatype proc proc?
  (procedure (vars (list-of identifier?))
             (body expression?)
             (saved-env environment?)))
; extend-env*: listof(identifier) x listof(vals) x env -> env
(define extend-env*
  (lambda (vars vals env)
    (cond ((= (length vars) (length vals))
           (cond ((null? vars) env)
                 (else (extend-env* (cdr vars)
                                    (cdr vals)
                                    (extend-env (car vars) (newref (car vals)) env)))))
          (else (eopl:error 'extend-env* "not enough arguments! ~% expected: ~s detected: ~s" (length vars) (length vals))))))
; apply-procedure: proc x val -> val
(define apply-procedure
  (lambda (proc1 vals)
    (cases proc proc1
      (procedure (vars body saved-env)
                 (value-of body (extend-env* vars vals saved-env))))))


; ------------------------------------------------------------------------------
; Interpreter

; run: string -> val
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

; value-of-program: program -> val
(define value-of-program
  (lambda (pgm)
    (initialize-store!)
    (cases program pgm (a-program (exp1) (value-of exp1 (init-env))))))

(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (diff-exp (exp1 exp2)
        (let ((val1 (value-of exp1 env))
              (val2 (value-of exp2 env)))
          (let ((num1 (expval->num val1))
                (num2 (expval->num val2)))
            (num-val (- num1 num2)))))
      (if-exp (exp1 exp2 exp3)
        (let ((val1 (value-of exp1 env)))
          (if (expval->bool val1)
              (value-of exp2 env)
              (value-of exp3 env))))
      (var-exp (var)
        (deref (apply-env env var)))
      (let-exp (vars exps body)
               (let ((env1 (extend-env-let vars exps env env)))
                 (value-of body env1)))
      (proc-exp (vars body)
                (proc-val (procedure vars body env)))
      (call-exp (rator rands)
                (apply-procedure (expval->proc (value-of rator env))
                                 (map (lambda (rand) (value-of rand env)) rands)))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((num1 (expval->num val1)))
                     (bool-val (zero? num1)))))
      (letrec-exp (funcs lvars bodys exp)
                  (value-of exp
                            (extend-env-rec* funcs lvars bodys env)))
      (assign-exp (var exp)
                  (begin (setref! (apply-env env var)
                                  (value-of exp env))
                         (num-val 27)))
      (begin-exp (fir-exp rest-exps)
                 (begin-val (cons fir-exp rest-exps) env))
      (newpair-exp (exp1 exp2)
                   (pair-val (make-pair (value-of exp1 env)
                                        (value-of exp2 env))))
      (left-exp (exp1)
                (left (expval->pair (value-of exp1 env))))
      (right-exp (exp1)
                 (right (expval->pair (value-of exp1 env))))
      (setleft-exp (exp1 exp2)
                   (begin (setleft (expval->pair (value-of exp1 env)) (value-of exp2 env))
                          (num-val 82)))
      (setright-exp (exp1 exp2)
                    (begin (setright (expval->pair (value-of exp1 env)) (value-of exp2 env))
                           (num-val 83)))
      (ref-exp (var)
               (ref-val (apply-env env var)))
      (setref-exp (var exp)
                  (let ((ref (expval->ref (value-of var env)))
                        (val (value-of exp env)))
                    (setref! ref val)))
      (deref-exp (var)
                 (let ((ref (expval->ref (value-of var env))))
                   (deref ref)))
      )))
(define begin-val
  (lambda (exps env)
    (if (= (length exps) 1)
        (value-of (car exps) env)
        (begin (value-of (car exps) env)
               (begin-val (cdr exps) env)))))
(define extend-env-let
  (lambda (vars exps env ori_env)
    (if (null? vars)
        env
        (extend-env-let (cdr vars)
                        (cdr exps)
                        (extend-env (car vars)
                                    (newref (value-of (car exps) ori_env))
                                    env)
                        ori_env))))
; ------------------------------------------------------------------------------
; A nice REPL for interactive use

(define read-eval-print
  (sllgen:make-rep-loop "-->" value-of-program
    (sllgen:make-stream-parser scanner-spec grammar)))


(run "let a = 3

in let b = 4

in let swap = proc (x) proc (y)

let temp = deref(x) in begin setref(x,deref(y)); setref(y,temp) end in begin ((swap ref a) ref b); -(a,b) end")
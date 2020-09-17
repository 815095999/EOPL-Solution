#lang eopl

; data-structure representation style
; ------------------------------------------------------------------------------
; Environments
(define identifier?
  (lambda (x)
    (and (symbol? x)
         (not (equal? x 'lambda)))))
(define schemeval?
  (lambda (x) #t))
(define-datatype environment environment?
  (empty-env)
  (extend-env (var identifier?)
              (val expval?)
              (env environment?))
  (extend-env-rec (p-names (list-of identifier?))
                  (vectors (list-of vector?)) (env environment?)))
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
                              (proc-val (procedure (car b-vars) (car bodys) env)))
                 (modify-vec vecs (cdr b-vars) (cdr bodys) env (+ num 1)))))
    (modify-vec vecs b-vars bodys new-env 0)))
(define extend-env-let
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-env (car vars) (car vals)
                    (extend-env-let (cdr vars) (cdr vals) env)))))
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
    (extend-env 'i (num-val 1)
      (extend-env 'v (num-val 5)
        (extend-env 'x (num-val 10)
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
    (expression ("proc" "(" (separated-list identifier ",") ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" expression) "in" expression) letrec-exp)
    (expression ("try" expression "catch" "(" identifier ")" expression) try-exp)
    (expression ("raise" expression) raise-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("null?" "(" expression ")") null-exp)
    (expression ("emptylist") emptylist-exp)
    (expression ("list" "(" (separated-list expression ",") ")") list-exp)
    (expression ("letcc" identifier "in" expression) letcc-exp)
    (expression ("throw" expression "to" expression) throw-exp)
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
; Expressed values
(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (proc-val (proc proc?))
  (pair-val (car1 expval?)
            (cdr1 expval?))
  (cont-val (cont continuation?))
  (emptylist-val)
)

; expval->car: expval -> expval
(define expval->car
  (lambda (val)
    (cases expval val
      (pair-val (car1 cdr1) car1)
      (else (report-expval-extractor-error 'pair val)))))
; expval->cdr: expval -> expval
(define expval->cdr
  (lambda (val)
    (cases expval val
      (pair-val (car1 cdr1) cdr1)
      (else (report-expval-extractor-error 'pair val)))))
; expval->num: expval -> num
(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (report-expval-extractor-error 'num val)))))
; expval->bool: expval -> bool
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

(define expval->cont
  (lambda (val)
    (cases expval val
      (cont-val (cont) cont)
      (else (report-expval-extractor-error 'cont-val val)))))
; list-reversed->expval: listof(expval) -> expval
(define list-reversed->expval
  (lambda (lst-rev)
    (define (trans lst vallst)
      (if (null? lst)
        vallst
        (trans (cdr lst)
               (pair-val (car lst)
                         vallst))))
    (trans lst-rev (emptylist-val))))
(define report-expval-extractor-error
  (lambda (expected val)
    (eopl:error 'expval-extractor "Expected a ~s, got ~s" expected val)))

; ------------------------------------------------------------------------------
; proc
(define-datatype proc proc?
  (procedure (var (list-of identifier?))
             (body expression?)
             (saved-env environment?)))

; apply-procedure: proc x val x cont -> finalanswer
(define apply-procedure/k
  (lambda (proc1 vals cont)
    (cases proc proc1
      (procedure (vars body saved-env)
                 (value-of/k body
                             (extend-env-let vars vals saved-env)
                             cont)))))

; ------------------------------------------------------------------------------
; Continuation (data-structure representation)
; cont: val -> finalanswer
; end-cont: () -> cont
(define-datatype continuation continuation?
  (end-cont)
  (zero1-cont (cont continuation?))
  (let-exp-cont (vars (list-of identifier?))
                (caled (list-of expval?))
                (uncal (list-of expression?))
                (body expression?)
                (env environment?)
                (cont continuation?))
  (if-test-cont (exp1 expression?)
                (exp2 expression?)
                (env environment?)
                (cont continuation?))
  (diff1-cont (exp2 expression?)
              (env environment?)
              (cont continuation?))
  (diff2-cont (val1 expval?)
              (cont continuation?))
  (call-cont (caled (list-of expval?))
             (uncal (list-of expression?))
             (env environment?)
             (cont continuation?))
  (try-cont (var identifier?)
            (exp1 expression?)
            (env environment?)
            (cont continuation?))
  (raise-cont (cont continuation?))
  (cons-car-cont (cdr1 expression?)
                 (env environment?)
                 (cont continuation?))
  (cons-cdr-cont (car1 expval?)
                 (cont continuation?))
  (car-cont (cont continuation?))
  (cdr-cont (cont continuation?))
  (null-cont (cont continuation?))
  (list-cont (caled (list-of expval?))
             (uncal (list-of expression?))
             (env environment?)
             (cont continuation?))
  (throw-cont (exp expression?)
              (env environment?)
              (cont continuation?))
  (throw2-cont (val expval?)
               (cont2 continuation?))
  )

; apply-cont: cont x val -> finalanswer
(define apply-cont
  (lambda (cont val)
    (cases continuation cont
      (end-cont ()
                (begin (eopl:printf "End of computation.~%")
                       val))
      (zero1-cont (cont)
                  (apply-cont cont
                              (bool-val (zero? (expval->num val)))))
      (let-exp-cont (vars caled uncal body env cont)
                    (let ((new-caled (append caled (list val))))
                      (if (null? uncal)
                          (value-of/k body (extend-env-let vars new-caled env) cont)
                          (value-of/k (car uncal) env (let-exp-cont vars new-caled (cdr uncal) body env cont)))))
      (if-test-cont (exp1 exp2 env cont)
                    (if (expval->bool val)
                        (value-of/k exp1 env cont)
                        (value-of/k exp2 env cont)))
      (diff1-cont (exp2 env cont)
                  (value-of/k exp2 env (diff2-cont val cont)))
      (diff2-cont (val1 cont)
                  (apply-cont cont (num-val (- (expval->num val1)
                                               (expval->num val)))))
      (call-cont (caled uncal env cont)
                 (if (null? uncal)
                     (cases expval (car caled)
                       (proc-val (proc)
                                 (apply-procedure/k proc (append (cdr caled) (list val)) cont))
                       (cont-val (cont)
                                 (apply-cont cont val))
                       (else (eopl:error 'call-cont "rator error!")))
                     (value-of/k (car uncal) env (call-cont (append caled (list val))
                                                            (cdr uncal)
                                                            env
                                                            cont))))
      (try-cont (var exp1 env cont)
                (apply-cont cont val))
      (raise-cont (cont)
                  (apply-handler val cont))
      (cons-car-cont (cdr1 env cont)
                     (value-of/k cdr1 env (cons-cdr-cont val cont)))
      (cons-cdr-cont (car1 cont)
                     (apply-cont cont (pair-val car1 val)))
      (car-cont (cont)
                (apply-cont cont (expval->car val)))
      (cdr-cont (cont)
                (apply-cont cont (expval->cdr val)))
      (null-cont (cont)
                 (apply-cont cont (bool-val (cases expval val
                                              (emptylist-val () #t)
                                              (pair-val (car1 cdr1) #f)
                                              (else (eopl:error 'null "not a pair! ~s" val))))))
      (list-cont (caled uncal env cont)
                 (if (null? uncal)
                     (apply-cont cont (list-reversed->expval (cons val caled)))
                     (value-of/k (car uncal) env (list-cont (cons val caled)
                                                            (cdr uncal)
                                                            env
                                                            cont))))
      (throw-cont (exp env cont)
                  (value-of/k exp env (throw2-cont val cont)))
      (throw2-cont (val2 cont)
                   (apply-cont (expval->cont val) val2))
      )))
; ------------------------------------------------------------------------------
; apply-handler
(define apply-handler
  (lambda (val cont)
    (cases continuation cont
      (try-cont (var handler-exp saved-env saved-cont)
                (value-of/k handler-exp
                            (extend-env var val saved-env)
                            saved-cont))
      (end-cont () (report-uncaught-exception))
      (zero1-cont (cont)
                  (apply-handler val cont))
      (let-exp-cont (vars caled uncal body env cont)
                    (apply-handler val cont))
      (if-test-cont (exp1 exp2 env cont)
                    (apply-handler val cont))
      (diff1-cont (exp2 env cont)
                  (apply-handler val cont))
      (diff2-cont (val1 cont)
                  (apply-handler val cont))
      (call-cont (caled uncal env cont)
                 (apply-handler val cont))
      (raise-cont (cont)
                  (apply-handler val cont))
      (cons-car-cont (cdr1 env cont)
                     (apply-handler val cont))
      (cons-cdr-cont (car1 cont)
                     (apply-handler val cont))
      (car-cont (cont)
                (apply-handler val cont))
      (cdr-cont (cont)
                (apply-handler val cont))
      (null-cont (cont)
                 (apply-handler val cont))
      (list-cont (caled uncal env cont)
                 (apply-handler val cont))
      (throw-cont (exp env cont)
                  (apply-handler val cont))
      (throw2-cont (val2 cont)
                   (apply-handler val cont))
      )))

(define report-uncaught-exception
  (lambda ()
    (eopl:error 'apply-handler "uncaught exception!")))
; ------------------------------------------------------------------------------
; Interpreter

; run: string -> finalanswer
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

; value-of-program: program -> finalanswer
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
        (value-of/k exp1 (init-env) (end-cont))))))

(define value-of/k
  (lambda (exp env cont)
    (cases expression exp
      (const-exp (num) (apply-cont cont (num-val num)))
      (var-exp (var)
               (apply-cont cont (apply-env env var)))
      (proc-exp (vars body)
                (apply-cont cont (proc-val (procedure vars body env))))
      (zero?-exp (exp1)
                 (value-of/k exp1 env (zero1-cont cont)))
      (let-exp (vars exps body)
               (value-of/k (car exps) env (let-exp-cont vars '() (cdr exps) body env cont)))
      (if-exp (exp1 exp2 exp3)
              (value-of/k exp1 env (if-test-cont exp2 exp3 env cont)))
      (diff-exp (exp1 exp2)
        (value-of/k exp1 env (diff1-cont exp2 env cont)))
      (call-exp (rator rands)
                (value-of/k rator env (call-cont '() rands env cont)))
      (letrec-exp (funcs lvars bodys exp)
                  (value-of/k exp
                             (extend-env-rec* funcs lvars bodys env)
                             cont))
      (try-exp (exp1 var exp2)
               (value-of/k exp1 env (try-cont var exp2 env cont)))
      (raise-exp (exp)
                 (value-of/k exp env (raise-cont cont)))
      (cons-exp (exp1 exp2)
                (value-of/k exp1 env (cons-car-cont exp2 env cont)))
      (car-exp (exp1)
               (value-of/k exp1 env (car-cont cont)))
      (cdr-exp (exp1)
               (value-of/k exp1 env (cdr-cont cont)))
      (null-exp (exp1)
                (value-of/k exp1 env (null-cont cont)))
      (emptylist-exp ()
                     (apply-cont cont (emptylist-val)))
      (list-exp (exps)
                (if (null? exps)
                    (apply-cont cont (emptylist-val))
                    (value-of/k (car exps) env (list-cont '()
                                                          (cdr exps)
                                                          env
                                                          cont))))
      (letcc-exp (var exp)
                 (value-of/k exp (extend-env var (cont-val cont) env) cont))
      (throw-exp (exp1 exp2)
                 (value-of/k exp1 env (throw-cont exp2 env cont)))
      )))
; ------------------------------------------------------------------------------
; A nice REPL for interactive use

(define read-eval-print
  (sllgen:make-rep-loop "-->" value-of-program
    (sllgen:make-stream-parser scanner-spec grammar)))

(run "let call-with-current-continuation = proc (p) letcc cont in (p proc(v) throw v to cont)
      in let y = proc (x) list((x 4),5)
         in -(3,(call-with-current-continuation y))")


(run "let call-with-current-continuation = proc (p) letcc cont in (p proc(v) throw v to cont)
      in let foo = proc (x) x
         in let bar = proc (x) 3
            in ((call-with-current-continuation foo) bar)")

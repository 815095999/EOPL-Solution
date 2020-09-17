#lang eopl

;; Exercise 6.36 [★★] Add a begin expression (exercise 4.4) to CPS-IN. You should not need to add anything to CPS-OUT.

;; CPS-IN grammar.

(define the-lexical-spec
  '([whitespace (whitespace) skip]
    [comment ("%" (arbno (not #\newline))) skip]
    [identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol]
    [number (digit (arbno digit)) number]
    [number ("-" digit (arbno digit)) number]))

(define the-grammar
  '([program (expression) a-program]
    [expression (number) const-exp]
    [expression ("-" "(" expression "," expression ")") diff-exp]
    [expression ("+" "(" (separated-list expression ",") ")") sum-exp]
    [expression ("zero?" "(" expression ")") zero?-exp]
    [expression ("if" expression "then" expression "else" expression) if-exp]
    [expression ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" expression) "in" expression) letrec-exp]
    [expression ("begin" expression (arbno ";" expression) "end") begin-exp]
    [expression (identifier) var-exp]
    [expression ("let" identifier "=" expression "in" expression) let-exp]
    [expression ("proc" "(" (arbno identifier) ")" expression) proc-exp]
    [expression ("(" expression (arbno expression) ")") call-exp]
    [expression ("print" "(" expression ")") print-exp]
    [expression ("newref" "(" expression ")") newref-exp]
    [expression ("deref" "(" expression ")") deref-exp]
    [expression ("setref" "(" expression "," expression ")") setref-exp]))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse (sllgen:make-string-parser the-lexical-spec the-grammar))

;; CPS-OUT grammar.

(define cps-out-lexical-spec
  '([whitespace (whitespace) skip]
    [comment ("%" (arbno (not #\newline))) skip]
    [identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol]
    [number (digit (arbno digit)) number]
    [number ("-" digit (arbno digit)) number]))

(define cps-out-grammar
  '([cps-out-program (tfexp) cps-a-program]
    [simple-expression (number) cps-const-exp]
    [simple-expression (identifier) cps-var-exp]
    [simple-expression ("-" "(" simple-expression "," simple-expression ")") cps-diff-exp]
    [simple-expression ("zero?" "(" simple-expression ")") cps-zero?-exp]
    [simple-expression ("+" "(" (separated-list simple-expression ",") ")") cps-sum-exp]
    [simple-expression ("proc" "(" (arbno identifier) ")" tfexp) cps-proc-exp]
    [tfexp (simple-expression) simple-exp->exp]
    [tfexp ("let" identifier "=" simple-expression "in" tfexp) cps-let-exp]
    [tfexp ("letrec" (arbno identifier "(" (arbno identifier) ")" "=" tfexp) "in" tfexp) cps-letrec-exp]
    [tfexp ("if" simple-expression "then" tfexp "else" tfexp) cps-if-exp]
    [tfexp ("(" simple-expression (arbno simple-expression) ")") cps-call-exp]
    [tfexp ("printk" "(" simple-expression ")" ";" tfexp) cps-printk-exp]
    [tfexp ("newrefk" "(" simple-expression "," simple-expression ")") cps-newrefk-exp]
    [tfexp ("derefk" "(" simple-expression "," simple-expression ")") cps-derefk-exp]
    [tfexp ("setrefk" "(" simple-expression "," simple-expression ")" ";" tfexp) cps-setrefk-exp]))

(sllgen:make-define-datatypes cps-out-lexical-spec cps-out-grammar)

;; Transformer.

(define list-set
  (lambda (lst n val)
    (cond [(null? lst) (eopl:error 'list-set "ran off end")]
          [(zero? n) (cons val (cdr lst))]
          [else (cons (car lst) (list-set (cdr lst) (- n 1) val))])))

(define fresh-identifier
  (let ([sn 0])
    (lambda (identifier)
      (set! sn (+ sn 1))
      (string->symbol (string-append (symbol->string identifier) "%" (number->string sn))))))

(define all-simple?
  (lambda (exps)
    (if (null? exps)
        #t
        (and (inp-exp-simple? (car exps))
             (all-simple? (cdr exps))))))

(define inp-exp-simple?
  (lambda (exp)
    (cases expression exp
      [const-exp (num) #t]
      [var-exp (var) #t]
      [diff-exp (exp1 exp2) (and (inp-exp-simple? exp1) (inp-exp-simple? exp2))]
      [zero?-exp (exp1) (inp-exp-simple? exp1)]
      [proc-exp (ids exp) #t]
      [sum-exp (exps) (all-simple? exps)]
      [else #f])))

(define make-send-to-cont
  (lambda (cont bexp)
    (cps-call-exp cont (list bexp))))

(define cps-of-zero?-exp
  (lambda (exp1 k-exp)
    (cps-of-exps (list exp1)
                 (lambda (new-rands)
                   (make-send-to-cont k-exp (cps-zero?-exp (car new-rands)))))))

(define cps-of-sum-exp
  (lambda (exps k-exp)
    (cps-of-exps exps
                 (lambda (new-rands)
                   (make-send-to-cont k-exp (cps-sum-exp new-rands))))))

(define cps-of-diff-exp
  (lambda (exp1 exp2 k-exp)
    (cps-of-exps (list exp1 exp2)
                 (lambda (new-rands)
                   (make-send-to-cont k-exp (cps-diff-exp (car new-rands) (cadr new-rands)))))))

(define cps-of-if-exp
  (lambda (exp1 exp2 exp3 k-exp)
    (cps-of-exps (list exp1)
                 (lambda (new-rands)
                   (cps-if-exp (car new-rands) (cps-of-exp exp2 k-exp) (cps-of-exp exp3 k-exp))))))

(define cps-of-let-exp
  (lambda (id rhs body k-exp)
    (cps-of-exps (list rhs)
                 (lambda (new-rands)
                   (cps-let-exp id (car new-rands) (cps-of-exp body k-exp))))))

(define cps-of-letrec-exp
  (lambda (proc-names idss proc-bodies body k-exp)
    (cps-letrec-exp proc-names
                    (map (lambda (ids)
                           (append ids (list 'k%00)))
                         idss)
                    (map (lambda (exp)
                           (cps-of-exp exp (cps-var-exp 'k%00)))
                         proc-bodies)
                    (cps-of-exp body k-exp))))

(define cps-of-begin-exp
  (lambda (exp1 exps k-exp)
    (cps-of-exps (cons exp1 exps)
                 (lambda (new-rands)
                   (make-send-to-cont k-exp
                                      (let loop ([head (car new-rands)]
                                                 [tail (cdr new-rands)])
                                        (if (null? tail)
                                            head
                                            (loop (car tail)
                                                  (cdr tail)))))))))

(define cps-of-call-exp
  (lambda (rator rands k-exp)
    (cps-of-exps (cons rator rands)
                 (lambda (new-rands)
                   (cps-call-exp (car new-rands) (append (cdr new-rands) (list k-exp)))))))

(define report-invalid-exp-to-cps-of-simple-exp
  (lambda (exp)
    (eopl:error 'cps-of-simple-exp "non-simple expression to cps-of-simple-exp: ~s" exp)))

(define cps-of-simple-exp
  (lambda (exp)
    (cases expression exp
      [const-exp (num) (cps-const-exp num)]
      [var-exp (var) (cps-var-exp var)]
      [diff-exp (exp1 exp2) (cps-diff-exp (cps-of-simple-exp exp1) (cps-of-simple-exp exp2))]
      [zero?-exp (exp1) (cps-zero?-exp (cps-of-simple-exp exp1))]
      [proc-exp (ids exp) (cps-proc-exp (append ids (list 'k%00)) (cps-of-exp exp (cps-var-exp 'k%00)))]
      [sum-exp (exps) (cps-sum-exp (map cps-of-simple-exp exps))]
      [else (report-invalid-exp-to-cps-of-simple-exp exp)])))

(define cps-of-exp
  (lambda (exp k-exp)
    (cases expression exp
      [const-exp (num) (make-send-to-cont k-exp (cps-const-exp num))]
      [var-exp (var) (make-send-to-cont k-exp (cps-var-exp var))]
      [proc-exp (vars body) (make-send-to-cont k-exp
                                               (cps-proc-exp (append vars (list 'k%00))
                                                             (cps-of-exp body (cps-var-exp 'k%00))))]
      [zero?-exp (exp1) (cps-of-zero?-exp exp1 k-exp)]
      [diff-exp (exp1 exp2) (cps-of-diff-exp exp1 exp2 k-exp)]
      [sum-exp (exps) (cps-of-sum-exp exps k-exp)]
      [if-exp (exp1 exp2 exp3) (cps-of-if-exp exp1 exp2 exp3 k-exp)]
      [let-exp (var exp1 body) (cps-of-let-exp var exp1 body k-exp)]
      [letrec-exp (ids bidss proc-bodies body) (cps-of-letrec-exp ids bidss proc-bodies body k-exp)]
      [begin-exp (exp1 exps) (cps-of-begin-exp exp1 exps k-exp)]
      [call-exp (rator rands) (cps-of-call-exp rator rands k-exp)]
      [print-exp (rator) (cps-of-exps (list rator)
                                      (lambda (simples)
                                        (cps-printk-exp (car simples) (make-send-to-cont k-exp (cps-const-exp 38)))))]
      [newref-exp (exp1) (cps-of-exps (list exp1)
                                      (lambda (simples)
                                        (cps-newrefk-exp (car simples) k-exp)))]
      [deref-exp (exp1) (cps-of-exps (list exp1)
                                     (lambda (simples)
                                       (cps-derefk-exp (car simples) k-exp)))]
      [setref-exp (exp1 exp2) (cps-of-exps (list exp1 exp2)
                                           (lambda (simples)
                                             (cps-setrefk-exp (car simples)
                                                              (cadr simples)
                                                              (make-send-to-cont k-exp (cps-const-exp 23)))))])))

(define cps-of-exps
  (lambda (exps builder)
    (define list-index
      (lambda (pred lst)
        (cond [(null? lst) #f]
              [(pred (car lst)) 0]
              [(list-index pred (cdr lst)) => (lambda (n)
                                                (+ n 1))]
              [else #f])))
    (let cps-of-rest ([exps exps])
      (let ([pos (list-index (lambda (exp)
                               (not (inp-exp-simple? exp)))
                             exps)])
        (if (not pos)
            (builder (map cps-of-simple-exp exps))
            (let ([var (fresh-identifier 'var)])
              (cps-of-exp (list-ref exps pos)
                          (cps-proc-exp (list var) (cps-of-rest (list-set exps pos (var-exp var)))))))))))

(define cps-of-program
  (lambda (pgm)
    (cases program pgm
      [a-program (exp1) (cps-a-program (cps-of-exps (list exp1)
                                                    (lambda (new-args)
                                                      (simple-exp->exp (car new-args)))))])))

;; Data structures - expressed values.

(define-datatype proc proc?
  [procedure [vars (list-of symbol?)]
             [body tfexp?]
             [env environment?]])

(define-datatype expval expval?
  [num-val [value number?]]
  [bool-val [boolean boolean?]]
  [proc-val [proc proc?]]
  [ref-val [ref reference?]])

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s" variant value)))

(define expval->num
  (lambda (v)
    (cases expval v
      [num-val (num) num]
      [else (expval-extractor-error 'num v)])))

(define expval->bool
  (lambda (v)
    (cases expval v
      [bool-val (bool) bool]
      [else (expval-extractor-error 'bool v)])))

(define expval->proc
  (lambda (v)
    (cases expval v
      [proc-val (proc) proc]
      [else (expval-extractor-error 'proc v)])))

(define expval->ref
  (lambda (v)
    (cases expval v
      [ref-val (ref) ref]
      [else (expval-extractor-error 'reference v)])))

;; Data structures - environment.

(define empty-env
  (lambda ()
    '()))

(define extend-env*
  (lambda (syms vals old-env)
    (cons (list 'let syms vals) old-env)))

(define extend-env-rec**
  (lambda (p-names b-varss p-bodies saved-env)
    (cons (list 'letrec p-names b-varss p-bodies) saved-env)))

(define environment?
  (list-of (lambda (p)
             (and (pair? p) (or (eqv? (car p) 'let) (eqv? (car p) 'letrec))))))

(define apply-env
  (lambda (env search-sym)
    (define list-index
      (lambda (sym los)
        (let loop ([pos 0]
                   [los los])
          (cond [(null? los) #f]
                [(eqv? sym (car los)) pos]
                [else (loop (+ pos 1) (cdr los))]))))
    (if (null? env)
        (eopl:error 'apply-env "No binding for ~s" search-sym)
        (let* ([binding (car env)]
               [saved-env (cdr env)])
          (let ([pos (list-index search-sym (cadr binding))])
            (if pos
                (case (car binding)
                  [(let) (list-ref (caddr binding) pos)]
                  [(letrec) (let ([bvars (caddr binding)]
                                  [bodies (cadddr binding)])
                              (proc-val (procedure (list-ref bvars pos) (list-ref bodies pos) env)))])
                (apply-env saved-env search-sym)))))))

;; Data structures - continuation.

(define-datatype continuation continuation?
  [end-cont])

;; Data structures - store.

(define reference?
  (lambda (v)
    (integer? v)))

(define the-store 'uninitialized)

(define empty-store
  (lambda ()
    '()))

(define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))

(define newref
  (lambda (val)
    (let ([next-ref (length the-store)])
      (set! the-store (append the-store (list val)))
      next-ref)))

(define deref
  (lambda (ref)
    (list-ref the-store ref)))

(define report-invalid-reference
  (lambda (ref the-store)
    (eopl:error 'setref "illegal reference ~s in store ~s" ref the-store)))

(define setref!
  (lambda (ref val)
    (set! the-store (letrec ([setref-inner (lambda (store1 ref1)
                                             (cond [(null? store1) (report-invalid-reference ref the-store)]
                                                   [(zero? ref1) (cons val (cdr store1))]
                                                   [else (cons (car store1) (setref-inner (cdr store1) (- ref1 1)))]))])
                      (setref-inner the-store ref)))))

;; Interpreter.

(define apply-cont
  (lambda (cont val)
    (cases continuation cont
      [end-cont () val])))

(define apply-procedure/k
  (lambda (proc1 args cont)
    (cases proc proc1
      [procedure (vars body saved-env) (value-of/k body (extend-env* vars args saved-env) cont)])))

(define value-of-simple-exp
  (lambda (exp env)
    (cases simple-expression exp
      [cps-const-exp (num) (num-val num)]
      [cps-var-exp (var) (apply-env env var)]
      [cps-diff-exp (exp1 exp2) (let ([val1 (expval->num (value-of-simple-exp exp1 env))]
                                      [val2 (expval->num (value-of-simple-exp exp2 env))])
                                  (num-val (- val1 val2)))]
      [cps-zero?-exp (exp1) (bool-val (zero? (expval->num (value-of-simple-exp exp1 env))))]
      [cps-sum-exp (exps) (let ([nums (map (lambda (exp)
                                             (expval->num (value-of-simple-exp exp env)))
                                           exps)])
                            (num-val (let sum-loop ([nums nums])
                                       (if (null? nums)
                                           0
                                           (+ (car nums) (sum-loop (cdr nums)))))))]
      [cps-proc-exp (vars body) (proc-val (procedure vars body env))])))

(define value-of/k
  (lambda (exp env cont)
    (cases tfexp exp
      [simple-exp->exp (bexp) (apply-cont cont (value-of-simple-exp bexp env))]
      [cps-let-exp (var exp1 body) (let ([val (value-of-simple-exp exp1 env)])
                                     (value-of/k body (extend-env* (list var) (list val) env) cont))]
      [cps-letrec-exp (p-names b-varss p-bodies letrec-body) (value-of/k letrec-body
                                                                         (extend-env-rec** p-names b-varss p-bodies env)
                                                                         cont)]
      [cps-if-exp (exp1 exp2 exp3) (value-of/k (if (expval->bool (value-of-simple-exp exp1 env))
                                                   exp2
                                                   exp3)
                                               env
                                               cont)]
      [cps-call-exp (rator rands) (let ([rator-proc (expval->proc (value-of-simple-exp rator env))]
                                        [rand-vals (map (lambda (bexp)
                                                          (value-of-simple-exp bexp env))
                                                        rands)])
                                    (apply-procedure/k rator-proc rand-vals cont))]
      [cps-printk-exp (simple body) (begin (eopl:printf "~s~%" (value-of-simple-exp simple env))
                                           (value-of/k body env cont))]
      [cps-newrefk-exp (simple1 simple2) (let ([val1 (value-of-simple-exp simple1 env)]
                                               [val2 (value-of-simple-exp simple2 env)])
                                           (let ([newval (ref-val (newref val1))])
                                             (apply-procedure/k (expval->proc val2) (list newval) cont)))]
      [cps-derefk-exp (simple1 simple2) (apply-procedure/k (expval->proc (value-of-simple-exp simple2 env))
                                                           (list (deref (expval->ref (value-of-simple-exp simple1
                                                                                                          env))))
                                                           cont)]
      [cps-setrefk-exp (simple1 simple2 body) (let ([ref (expval->ref (value-of-simple-exp simple1 env))]
                                                    [val (value-of-simple-exp simple2 env)])
                                                (begin (setref! ref val)
                                                       (value-of/k body env cont)))])))

(define value-of-program
  (lambda (pgm)
    (initialize-store!)
    (cases cps-out-program pgm
      [cps-a-program (body) (value-of/k body (empty-env) (end-cont))])))

;; Interface.

(define run
  (lambda (string)
    (let ([cpsed-pgm (cps-of-program (scan&parse string))])
      (value-of-program cpsed-pgm))))

(provide bool-val num-val run)

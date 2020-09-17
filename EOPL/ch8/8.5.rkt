#lang eopl

; ------------------------------------------------------------------------------
; Scanner and parser specification


(define identifier? symbol?)
(define scanner-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    (identifier (letter (arbno (or letter digit "_" "-" "?"))) symbol)))

(define grammar
  '((program ((arbno module-definition) expression) a-program)
    (module-definition ("module" identifier "interface" interface "body" module-body)
                       a-module-definition)
    (decl (identifier ":" type) val-decl)
    (defn (identifier "=" expression) val-defn)
    (interface ("[" (arbno decl) "]") simple-iface)
    (module-body ("[" (arbno defn) "]") defns-module-body)
    (module-body ("let" (arbno identifier "=" expression) "in" module-body) let-module-body)
    (module-body ("letrec" (arbno type identifier "(" (arbno identifier ":" type) ")" "="
                                 expression) "in" module-body) letrec-module-body)
    (expression ("from" identifier "take" identifier) qualified-var-exp)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("proc" "(" (arbno identifier ":" type) ")" expression) proc-exp)
    (expression ("letrec" (arbno type identifier "(" (arbno identifier ":" type) ")" "="
                                 expression) "in" expression) letrec-exp)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("(" (arbno type) "->" type ")") proc-type)
    ))
 
(sllgen:make-define-datatypes scanner-spec grammar)

(define scan&parse
  (sllgen:make-string-parser scanner-spec grammar))


; ------------------------------------------------------------------------------
; Data structures

; decl->name : decl -> name
(define decl->name
  (lambda (decl1)
    (cases decl decl1
      (val-decl (name ty)
                name))))

; decl->type : decl -> type
(define decl->type
  (lambda (decl1)
    (cases decl decl1
      (val-decl (name ty)
                ty))))

(define-datatype proc proc?
  (procedure (var (list-of identifier?))
             (body expression?)
             (saved-env environment?)))

(define-datatype expval expval?
  [num-val [value number?]]
  [bool-val [boolean boolean?]]
  [proc-val [proc proc?]])

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

(define-datatype environment environment?
  [empty-env]
  [extend-env [bvar symbol?]
              [bval expval?]
              [saved-env environment?]]
  [extend-env-rec [p-names (list-of symbol?)]
                  [vectors (list-of vector?)]
                  [saved-env environment?]]
  [extend-env-with-module [m-name symbol?]
                          [m-val typed-module?]
                          [saved-env environment?]])

(define extend-env*
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-env (car vars) (car vals)
                    (extend-env* (cdr vars) (cdr vals) env)))))

(define extend-env-rec*
  (lambda (p-names b-varss p-bodies env)
    (define (generate-vec num)
      (if (= num 0)
          '()
          (cons (make-vector 1) (generate-vec (- num 1)))))
    (define vecs (generate-vec (length p-names)))
    (define new-env (extend-env-rec p-names vecs env))
    (define (modify-vec vecs b-varss p-bodies env num)
      (if (null? b-varss)
          env
          (begin (vector-set! (list-ref vecs num) 0
                              (proc-val (procedure (car b-varss) (car p-bodies) env)))
                 (modify-vec vecs (cdr b-varss) (cdr p-bodies) env (+ num 1)))))
    (modify-vec vecs b-varss p-bodies new-env 0)))

(define extract-procedure
  (lambda (p-names vecs search-var num)
    (if (equal? search-var (car p-names))
        (vector-ref (list-ref vecs num) 0)
        (extract-procedure (cdr p-names) vecs search-var (+ num 1)))))

(define apply-env
  (lambda (env search-var)
    (cases environment env
      [empty-env ()
                 (report-no-binding-found search-var)]
      [extend-env (saved-var saved-val saved-env)
                  (if (equal? saved-var search-var)
                      saved-val
                      (apply-env saved-env search-var))]
      [extend-env-rec (p-names vecs saved-env)
                      (if (memq search-var p-names)
                          (extract-procedure p-names vecs search-var 0)
                          (apply-env saved-env search-var))]
      [extend-env-with-module (m-name m-val saved-env)
                              (if (eqv? search-var m-name)
                                  m-val
                                  (apply-env saved-env search-var))])))

(define-datatype tenvironment tenvironment?
  (empty-tenv)
  (extend-tenv (var identifier?)
               (val type?)
               (tenv tenvironment?))
  (extend-tenv-with-module (name symbol?)
                           (interface interface?)
                           (saved-tenv tenvironment?)))


(define extend-tenv*
  (lambda (vars types tenv)
    (if (null? vars)
        tenv
        (extend-tenv (car vars)
                     (car types)
                     (extend-tenv* (cdr vars)
                                   (cdr types)
                                   tenv)))))
(define extend-tenv-rec
  (lambda (p-names p-var-typess p-result-types tenv)
    (if (null? p-names)
        tenv
        (extend-tenv (car p-names)
                     (proc-type (car p-var-typess)
                                (car p-result-types))
                     (extend-tenv-rec (cdr p-names)
                                      (cdr p-var-typess)
                                      (cdr p-result-types)
                                      tenv)))))

(define apply-tenv
  (lambda (tenv search-var)
    (cases tenvironment tenv
      (empty-tenv ()
                  (report-no-binding-found search-var))
      (extend-tenv (saved-var saved-val saved-tenv)
                   (if (equal? saved-var search-var)
                       saved-val
                       (apply-tenv saved-tenv search-var)))
      (extend-tenv-with-module (name interface saved-tenv)
                               (if (equal? name search-var)
                                   interface
                                   (apply-tenv saved-tenv search-var))))))


(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-tenv "No binding for ~s" search-var)))


; ------------------------------------------------------------------------------
; Modules
(define-datatype typed-module typed-module?
  (simple-module
   (bindings environment?)))

; loopup-qualified-var-in-env : sym x sym x env -> expval
(define loopup-qualified-var-in-env
  (lambda (m-name var-name env)
    (let ((m-val (apply-env env m-name)))
      (cases typed-module m-val
        (simple-module (bindings)
                       (apply-env bindings var-name))))))

; loopup-qualified-var-in-tenv : sym x sym x tenv -> type
(define loopup-qualified-var-in-tenv
  (lambda (m-name var-name tenv)
    (let ((iface (apply-tenv tenv m-name)))
      (cases interface iface
        (simple-iface (decls)
                      (loopup-variable-name-in-decls var-name decls))))))

; loopup-variable-name-in-decls : sym x listof(decl) -> type
(define loopup-variable-name-in-decls
  (lambda (var decls)
    (if (null? decls)
        (eopl:error 'loopup-variable-namae-in-decls "~s not found" var)
        (cases decl (car decls)
          (val-decl (var1 ty)
                    (if (equal? var1 var)
                        ty
                        (loopup-variable-name-in-decls var (cdr decls))))))))
(define dot-split
  (lambda (str)
    (let loop ([str str]
               [count 0])
      (if (char=? #\. (string-ref str count))
          (cons (substring str 0 count)
                (substring str (+ count 1)))
          (loop str (+ count 1))))))
(define module-var->m-name
  (lambda (module-var)
    (string->symbol (car (dot-split (symbol->string module-var))))))
(define module-var->var
  (lambda (module-var)
    (string->symbol (cdr (dot-split (symbol->string module-var))))))


; ------------------------------------------------------------------------------
; the checker

; check-equal-type! : type x type x exp -> unspecified
(define check-equal-type!
  (lambda (ty1 ty2 exp)
    (if (not (equal? ty1 ty2))
        (report-unequal-types ty1 ty2 exp)
        #t)))

; report-unequal-types : type x type x exp -> unspecified
(define report-unequal-types
  (lambda (ty1 ty2 exp)
    (eopl:error 'check-equal-type!
                "Types didn't match: ~s != ~a in ~% ~a"
                (type-to-external-form ty1)
                (type-to-external-form ty2)
                exp)))

; type-to-external-form : type -> list
(define type-to-external-form
  (lambda (ty)
    (cases type ty
      (int-type () 'int)
      (bool-type () 'bool)
      (proc-type (arg-types result-type)
                 (append (map (lambda (x) (type-to-external-form x)) arg-types)
                         (list '->
                               (type-to-external-form result-type)))))))

(define report-rator-not-a-proc-type
  (lambda (rator-type rator)
    (eopl:error 'rator-type-error "rator ~s has type ~s" rator rator-type)))

(define external-iface
  (lambda (iface)
    (cases interface iface
      (simple-iface (decls)
                    (map (lambda (decl1)
                           (cases decl decl1
                             (val-decl (var ty)
                                       (list var
                                             (type-to-external-form ty)))))
                         decls)))))
; ------------------------------------------------------------------------------
; type-of-program : program -> type
(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (module-defns body)
                 (type-of body
                          (add-module-defns-to-tenv module-defns (empty-tenv)))))))
; add-module-defns-to-tenv : listof(module-defn) x tenv -> tenv
(define add-module-defns-to-tenv
  (lambda (defns tenv)
    (if (null? defns)
        tenv
        (cases module-definition (car defns)
          (a-module-definition (m-name expected-iface m-body)
                               (let ((actual-iface (interface-of m-body tenv)))
                                 (if (<:-iface actual-iface expected-iface tenv)
                                     (let ((new-tenv
                                            (extend-tenv-with-module
                                             m-name
                                             expected-iface
                                             tenv)))
                                       (add-module-defns-to-tenv
                                        (cdr defns) new-tenv))
                                     (report-module-doesnt-satisfy-iface
                                      m-name expected-iface actual-iface))))))))
(define report-module-doesnt-satisfy-iface
  (lambda (m-name expected-iface actual-iface)
    (eopl:error 'module-doesnt-satisfy-iface "~% ~s ~% doesn't match ~% ~s in ~s"
                (external-iface expected-iface)
                (external-iface actual-iface) m-name)))

; interface-of : module-body x tenv -> iface
(define interface-of
  (lambda (m-body tenv)
    (cases module-body m-body
      (defns-module-body (defns)
        (simple-iface (defns-to-decls defns tenv)))
      (let-module-body (vars exps defns)
                       (let ((exp-types (map (lambda (x) (type-of x tenv)) exps)))
                         (interface-of defns (extend-tenv* vars exp-types tenv))))
      (letrec-module-body (p-result-types p-names b-varss b-var-typess p-bodies defns)
                  (let ((tenv-for-letrec-body
                         (extend-tenv-rec p-names b-var-typess p-result-types tenv)))
                    (let ((p-body-types
                           (types-of-p-bodies b-varss b-var-typess p-bodies tenv-for-letrec-body)))
                      (check-equal-type! p-body-types p-result-types p-bodies)
                      (interface-of defns tenv-for-letrec-body)))))))

; defns-to-decls : listof(defn) x tenv -> listof(decl)
(define defns-to-decls
  (lambda (defns tenv)
    (if (null? defns)
        '()
        (cases defn (car defns)
          (val-defn (var-name exp)
                    (let ((ty (type-of exp tenv)))
                      (cons (val-decl var-name ty)
                            (defns-to-decls
                              (cdr defns)
                              (extend-tenv var-name ty tenv)))))))))
; <:-iface : iface x iface x tenv -> bool
(define <:-iface
  (lambda (iface1 iface2 tenv)
    (cases interface iface1
      (simple-iface (decls1)
                    (cases interface iface2
                      (simple-iface (decls2)
                                    (<:-decls decls1 decls2 tenv)))))))
; <:-decls : listof(decl) x listof(decl) x tenv -> bool
(define <:-decls
  (lambda (decls1 decls2 tenv)
    (cond ((null? decls2) #t)
          ((null? decls1) #f)
          (else (let ((name1 (decl->name (car decls1)))
                      (name2 (decl->name (car decls2))))
                  (if (eqv? name1 name2)
                      (and (equal?
                            (decl->type (car decls1))
                            (decl->type (car decls2)))
                           (<:-decls (cdr decls1) (cdr decls2) tenv))
                      (<:-decls (cdr decls1) decls2 tenv)))))))


; run: string -> finalanswer
(define run-type
  (lambda (string)
    (type-to-external-form (type-of-program (scan&parse string)))))

; type-of : exp x tenv -> type
(define type-of
  (lambda (exp tenv)
    (cases expression exp
      (const-exp (num) (int-type))
      (var-exp (var) (apply-tenv tenv var))
      (diff-exp (exp1 exp2)
                (let ((ty1 (type-of exp1 tenv))
                      (ty2 (type-of exp2 tenv)))
                  (check-equal-type! ty1 (int-type) exp1)
                  (check-equal-type! ty2 (int-type) exp2)
                  (int-type)))
      (zero?-exp (exp1)
                 (let ((ty1 (type-of exp1 tenv)))
                   (check-equal-type! ty1 (int-type) exp1)
                   (bool-type)))
      (if-exp (exp1 exp2 exp3)
              (let ((ty1 (type-of exp1 tenv))
                    (ty2 (type-of exp2 tenv))
                    (ty3 (type-of exp3 tenv)))
                (check-equal-type! ty1 (bool-type) exp1)
                (check-equal-type! ty2 ty3 exp)
                ty2))
      (let-exp (vars exps body)
               (let ((exp-types (map (lambda (x) (type-of x tenv)) exps)))
                 (type-of body (extend-tenv* vars exp-types tenv))))
      (proc-exp (vars var-types body)
                (let ((result-type (type-of body
                                            (extend-tenv* vars var-types tenv))))
                  (proc-type var-types result-type)))
      (call-exp (rator rands)
                (let ((rator-type (type-of rator tenv))
                      (rand-types (map (lambda (x) (type-of x tenv)) rands)))
                  (cases type rator-type
                    (proc-type (arg-types result-type)
                               (begin (check-equal-type! arg-types rand-types rands)
                                      result-type))
                    (else (report-rator-not-a-proc-type rator-type rator)))))
      (letrec-exp (p-result-types p-names b-varss b-var-typess p-bodies letrec-body)
                  (let ((tenv-for-letrec-body
                         (extend-tenv-rec p-names b-var-typess p-result-types tenv)))
                    (let ((p-body-types
                           (types-of-p-bodies b-varss b-var-typess p-bodies tenv-for-letrec-body)))
                      (check-equal-type! p-body-types p-result-types p-bodies)
                      (type-of letrec-body tenv-for-letrec-body))))
      (qualified-var-exp (m-var var1)
                         (loopup-qualified-var-in-tenv m-var var1 tenv))
      )))


(define types-of-p-bodies
  (lambda (b-varss b-var-typess p-bodies tenv)
    (if (null? b-varss)
        '()
        (cons (type-of (car p-bodies)
                       (extend-tenv* (car b-varss)
                                    (car b-var-typess)
                                    tenv))
              (types-of-p-bodies (cdr b-varss)
                                (cdr b-var-typess)
                                (cdr p-bodies)
                                tenv)))))

; ------------------------------------------------------------------------------
; value-of-program : program -> expval
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (m-defns body)
                 (value-of body
                           (add-module-defns-to-env m-defns (empty-env)))))))

; add-module-defns-to-env : listof(moduledefn) x env -> env
(define add-module-defns-to-env
  (lambda (defns env)
    (if (null? defns)
        env
        (cases module-definition (car defns)
               (a-module-definition (m-name iface m-body)
                                    (add-module-defns-to-env
                                     (cdr defns)
                                     (extend-env-with-module
                                      m-name
                                      (value-of-module-body m-body env)
                                      env)))))))

; value-of-module-body : modulebody x env -> typedmodule
(define value-of-module-body
  (lambda (m-body env)
    (cases module-body m-body
      (defns-module-body (defns)
        (simple-module (defns-to-env defns env)))
      (let-module-body (vars exps defns)
                       (value-of-module-body defns (extend-env* vars
                                                                (map (lambda (x) (value-of x env)) exps)
                                                                env)))
      (letrec-module-body (p-result-types p-names b-varss b-var-types p-bodies defns)
                          (value-of-module-body defns (extend-env-rec* p-names b-varss p-bodies env))))))

; defns-to-env : listof(defn) x env -> env
(define defns-to-env
  (lambda (defns env)
    (if (null? defns)
        (empty-env)
        (cases defn (car defns)
          (val-defn (var exp)
                    (let ((val (value-of exp env)))
                      (let ((new-env (extend-env var val env)))
                        (extend-env var val
                                    (defns-to-env (cdr defns) new-env)))))))))

(define apply-procedure
  (lambda (proc1 rands)
    (cases proc proc1
      (procedure (b-vars body env)
                 (value-of body (extend-env* b-vars rands env))))))

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
        (apply-env env var))
      (let-exp (vars exps body)
               (value-of body (extend-env* vars
                                           (map (lambda (x) (value-of x env)) exps)
                                           env)))
      (proc-exp (vars var-types body)
                (proc-val (procedure vars body env)))
      (call-exp (rator rands)
                (apply-procedure (expval->proc (value-of rator env))
                                 (map (lambda (x) (value-of x env)) rands)))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((num1 (expval->num val1)))
                     (bool-val (zero? num1)))))
      (letrec-exp (p-result-types p-names b-varss b-var-types p-bodies letrec-body)
                  (value-of letrec-body
                            (extend-env-rec* p-names b-varss p-bodies env)))
      (qualified-var-exp (m-name var1)
                         (loopup-qualified-var-in-env m-name var1 env))
      )))


(define run-val
  (lambda (string)
    (let ((pgm1 (scan&parse string)))
      (type-of-program pgm1)
      (value-of-program pgm1))))

(run-val "module m1
             interface [a : int b : int c : int]
            body [a = 33 x = -(a,1) b = -(a,x) c = -(x,b)] 
            let a = 10 in -(-(from m1 take a,from m1 take b), a)")
(run-val "module m1
           interface [u : int]
           body [u = 44]
          module m2
           interface [v : int]
           body [v = -(from m1 take u,11)]
          -(from m1 take u, from m2 take v)")
(run-val "module m1
           interface [u:int v:int]
           body[u = 44 u = 33 v = -(u,11)]
           -(from m1 take u , from m1 take v)")   ; 多次定义取第一次

(run-val "module m1
           interface [u:int v:int]
           body[u = letrec int odd(x:int) = if zero?(x) then 0 else (even -(x,1))
                           int even(x:int) = if zero?(x) then 1 else (odd -(x,1))
                   in (odd 1) u = 33 v = -(u,11)]
           -(from m1 take u , from m1 take v)")

(run-val "module m1
           interface [u:int v:int]
           body[u = letrec int odd(x:int) = if zero?(x) then 0 else (even -(x,1))
                           int even(x:int) = if zero?(x) then 1 else (odd -(x,1))
                   in (odd 1) u = 33 v = -(u,11)]
           letrec int sum(x:int y:int) = -(x,-(0,y))
                  int pw2(x:int y:int) = if zero?(y) then x else (pw2 (sum x x) -(y,1))
                  in let x = from m1 take u
                         y = from m1 take v
                     in (sum (pw2 x y) (pw2 y x))")

(run-type "module even-odd
            interface [even : (int -> bool)
                       odd : (int -> bool)]
            body letrec bool local-odd (x : int) = if zero?(x) then zero?(1) else (local-even -(x,1))
                        bool local-even (x : int) = if zero?(x) then zero?(0) else (local-odd -(x,1))
                 in [even = local-even
                     odd = local-odd]
            from even-odd take even")

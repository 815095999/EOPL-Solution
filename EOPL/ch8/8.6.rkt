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
    (module-body (module-definition module-body) embeded-module-body)
    (expression ("from" identifier "take" identifier) qualified-var-exp)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("proc" "(" identifier ":" type ")" expression) proc-exp)
    (expression ("letrec" type identifier "(" identifier ":" type ")" "="
                          expression "in" expression) letrec-exp)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("(" type "->" type ")") proc-type)
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
  [procedure [bvar symbol?]
             [body expression?]
             [env environment?]])

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
  [extend-env-rec [p-name symbol?]
                  [b-var symbol?]
                  [p-body expression?]
                  [saved-env environment?]]
  [extend-env-with-module [m-name symbol?]
                          [m-val typed-module?]
                          [saved-env environment?]])


(define apply-env
  (lambda (env search-sym)
    (cases environment env
      [empty-env () (eopl:error 'apply-env "No binding for ~s" search-sym)]
      [extend-env (var val saved-env) (if (eqv? search-sym var)
                                          val
                                          (apply-env saved-env search-sym))]
      [extend-env-rec (p-name b-var p-body saved-env) (if (eqv? search-sym p-name)
                                                          (proc-val (procedure b-var p-body env))
                                                          (apply-env saved-env search-sym))]
      [extend-env-with-module (m-name m-val saved-env)
                              (if (eqv? search-sym m-name)
                                  m-val
                                  (apply-env saved-env search-sym))])))

(define-datatype tenvironment tenvironment?
  (empty-tenv)
  (extend-tenv (var identifier?)
               (val type?)
               (tenv tenvironment?))
  (extend-tenv-with-module (name symbol?)
                           (interface interface?)
                           (saved-tenv tenvironment?)))
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
      (proc-type (arg-type result-type)
                 (list (type-to-external-form arg-type)
                       '->
                       (type-to-external-form result-type))))))

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

(define add-module-to-tenv
  (lambda (mod1 tenv)
    (cases module-definition mod1
          (a-module-definition (m-name expected-iface m-body)
                               (let ((actual-iface (interface-of m-body tenv)))
                                 (if (<:-iface actual-iface expected-iface tenv)
                                     (extend-tenv-with-module
                                      m-name
                                      expected-iface
                                      tenv)
                                     (report-module-doesnt-satisfy-iface
                                      m-name expected-iface actual-iface)))))))
; add-module-defns-to-tenv : listof(module-defn) x tenv -> tenv
(define add-module-defns-to-tenv
  (lambda (defns tenv)
    (if (null? defns)
        tenv
        (add-module-defns-to-tenv
         (cdr defns) (add-module-to-tenv (car defns) tenv)))))
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
      (embeded-module-body (mod1 submod)
                           (interface-of submod (add-module-to-tenv mod1 tenv))))))

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
      (let-exp (var exp1 body)
               (let ((exp1-type (type-of exp1 tenv)))
                 (type-of body (extend-tenv var exp1-type tenv))))
      (proc-exp (var var-type body)
                (let ((result-type (type-of body
                                            (extend-tenv var var-type tenv))))
                  (proc-type var-type result-type)))
      (call-exp (rator rand)
                (let ((rator-type (type-of rator tenv))
                      (rand-type (type-of rand tenv)))
                  (cases type rator-type
                    (proc-type (arg-type result-type)
                               (begin (check-equal-type! arg-type rand-type rand)
                                      result-type))
                    (else (report-rator-not-a-proc-type rator-type rator)))))
      (letrec-exp (p-result-type p-name b-var b-var-type p-body letrec-body)
                  (let ((tenv-for-letrec-body
                         (extend-tenv p-name (proc-type b-var-type p-result-type) tenv)))
                    (let ((p-body-type
                           (type-of p-body (extend-tenv b-var b-var-type tenv-for-letrec-body))))
                      (check-equal-type! p-body-type p-result-type p-body)
                      (type-of letrec-body tenv-for-letrec-body))))
      (qualified-var-exp (m-var var1)
                         (loopup-qualified-var-in-tenv m-var var1 tenv))
      )))


; ------------------------------------------------------------------------------
; value-of-program : program -> expval
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (m-defns body)
                 (value-of body
                           (add-module-defns-to-env m-defns (empty-env)))))))

(define add-module-to-env
  (lambda (mod1 env)
    (cases module-definition mod1
      (a-module-definition (m-name iface m-body)
                           (extend-env-with-module
                            m-name
                            (value-of-module-body m-body env)
                            env)))))
; add-module-defns-to-env : listof(moduledefn) x env -> env
(define add-module-defns-to-env
  (lambda (defns env)
    (if (null? defns)
        env
        (add-module-defns-to-env
         (cdr defns)
         (add-module-to-env (car defns) env)))))

; value-of-module-body : modulebody x env -> typedmodule
(define value-of-module-body
  (lambda (m-body env)
    (cases module-body m-body
      (defns-module-body (defns)
        (simple-module (defns-to-env defns env)))
      (embeded-module-body (mod1 sub-mod)
                           (value-of-module-body sub-mod
                                                 (add-module-to-env mod1 env))))))

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
  (lambda (proc1 rand)
    (cases proc proc1
      (procedure (b-var body env)
                 (value-of body (extend-env b-var rand env))))))

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
      (let-exp (var1 exp1 body)
                (value-of body (extend-env var1
                                           (value-of exp1 env)
                                           env)))
      (proc-exp (var var-type body)
                (proc-val (procedure var body env)))
      (call-exp (rator rand)
                (apply-procedure (expval->proc (value-of rator env))
                                 (value-of rand env)))
      (zero?-exp (exp1)
                 (let ((val1 (value-of exp1 env)))
                   (let ((num1 (expval->num val1)))
                     (bool-val (zero? num1)))))
      (letrec-exp (p-result-type p-name b-var b-var-type p-body letrec-body)
                  (value-of letrec-body
                            (extend-env-rec p-name b-var p-body env)))
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
             interface [u : int v : int]
             body
               module m2
                 interface [v : int]
                 body
                  module m3
                  interface [u : int]
                  body [u = 33]
                 [v = from m3 take u]
              [u = 44
               v = -(from m2 take v, 1)]
         from m1 take v")
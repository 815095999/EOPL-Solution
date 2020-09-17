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
    (declarition (identifier ":" type) val-decl)
    (declarition ("opaque" identifier) opaque-type-decl)
    (declarition ("transparent" identifier "=" type) transparent-type-decl)
    (defn (identifier "=" expression) val-defn)
    (defn ("type" identifier "=" type) type-defn)
    (interface ("[" (arbno declarition) "]") simple-iface)
    (module-body ("[" (arbno defn) "]") defns-module-body)
    (expression ("from" identifier "take" identifier) qualified-var-exp)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("proc" "(" (arbno identifier ":" type) ")" expression) proc-exp)
    (expression ("letrec" type identifier "(" (arbno identifier ":" type) ")" "="
                          expression "in" expression) letrec-exp)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("(" (arbno type) "->" type ")") proc-type)
    (type (identifier) named-type)
    (type ("from" identifier "take" identifier) qualified-type)
    ))
 
(sllgen:make-define-datatypes scanner-spec grammar)

(define scan&parse
  (sllgen:make-string-parser scanner-spec grammar))


; ------------------------------------------------------------------------------
; Data structures

; decl->name : decl -> name
(define decl->name
  (lambda (decl1)
    (cases declarition decl1
      (val-decl (name ty)
                name)
      (opaque-type-decl (name) name)
      (transparent-type-decl (name ty) name))))

; decl->type : decl -> type
(define decl->type
  (lambda (decl1)
    (cases declarition decl1
      (val-decl (name ty)
                ty)
      (transparent-type-decl (name ty)
                             ty)
      (else (eopl:error 'decl->type "~s doesn't have type " decl1)))))

; transparent-type-decl? : decl -> bool
(define transparent-type-decl?
  (lambda (x)
    (cases declarition x
      (transparent-type-decl (name ty) #t)
      (else #f))))

; opaque-type-decl? : decl -> bool
(define opaque-type-decl?
  (lambda (x)
    (cases declarition x
      (opaque-type-decl (name) #t)
      (else #f))))

; val-decl? : decl -> bool
(define val-decl?
  (lambda (x)
    (cases declarition x
      (val-decl (name ty) #t)
      (else #f))))

(define-datatype proc proc?
  [procedure [bvar (list-of symbol?)]
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

; extend-env* : listof(sym) x listof(expval) x env -> env
(define extend-env*
  (lambda (vars vals env)
    (if (null? vars)
        env
        (extend-env* (cdr vars)
                     (cdr vals)
                     (extend-env (car vars)
                                 (car vals)
                                 env)))))
(define apply-env
  (lambda (env search-sym)
    (cases environment env
      [empty-env () (eopl:error 'apply-env "No binding for ~s" search-sym)]
      [extend-env (var val saved-env) (if (eqv? search-sym var)
                                          val
                                          (apply-env saved-env search-sym))]
      [extend-env-rec (p-name b-vars p-body saved-env) (if (eqv? search-sym p-name)
                                                          (proc-val (procedure b-vars p-body env))
                                                          (apply-env saved-env search-sym))]
      [extend-env-with-module (m-name m-val saved-env)
                              (apply-env saved-env search-sym)])))

(define-datatype tenvironment tenvironment?
  (empty-tenv)
  (extend-tenv (var symbol?)
               (val type?)
               (tenv tenvironment?))
  (extend-tenv-with-module (name symbol?)
                           (interface interface?)
                           (saved-tenv tenvironment?))
  (extend-tenv-with-type (name symbol?)
                         (type type?)
                         (saved-tenv tenvironment?)))

; extend-tenv* : listof(sym) x listof(type) x tenv -> tenv
(define extend-tenv*
  (lambda (vars tys tenv)
    (if (null? vars)
        tenv
        (extend-tenv* (cdr vars)
                      (cdr tys)
                      (extend-tenv (car vars)
                                   (car tys)
                                   tenv)))))
; expand-type : type x tenv -> expandedtype
(define expand-type
  (lambda (ty tenv)
    (cases type ty
      (int-type () ty)
      (bool-type () ty)
      (proc-type (arg-types result-type)
                 (proc-type (map (lambda (x) (expand-type x tenv)) arg-types)
                            (expand-type result-type tenv)))
      (named-type (name)
                  (lookup-type-name-in-tenv tenv name))
      (qualified-type (m-name t-name)
                      (lookup-qualified-type-in-tenv m-name t-name tenv)))))
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
                               (apply-tenv saved-tenv search-var))
      (extend-tenv-with-type (name ty saved-tenv)
                             (apply-tenv saved-tenv search-var)))))

(define report-no-binding-found
  (lambda (search-var)
    (eopl:error 'apply-tenv "No binding for ~s" search-var)))


; ------------------------------------------------------------------------------
; Modules
(define-datatype typed-module typed-module?
  (simple-module
   (bindings environment?)))

; lookup-module-name-in-env : env x sym -> module
(define lookup-module-name-in-env
  (lambda (env name)
    (cases environment env
      (empty-env () (eopl:error 'lookup-module-name-in-env "unbounded ~s" name))
      (extend-env (var val saved-env)
                  (lookup-module-name-in-env saved-env name))
      (extend-env-rec (p-name b-var p-body saved-env)
                      (lookup-module-name-in-env saved-env name))
      (extend-env-with-module (var val saved-env)
                              (if (equal? var name)
                                  val
                                  (lookup-module-name-in-env saved-env name))))))
; lookup-qualified-var-in-env : sym x sym x env -> expval
(define lookup-qualified-var-in-env
  (lambda (m-name var-name env)
    (let ((m-val (lookup-module-name-in-env env m-name)))
      (cases typed-module m-val
        (simple-module (bindings)
                       (apply-env bindings var-name))))))

; lookup-qualified-type-in-tenv : sym x sym x env -> type
(define lookup-qualified-type-in-tenv
  (lambda (m-name t-name tenv)
    (let ((m-val (lookup-module-name-in-tenv tenv m-name)))
      (cases interface m-val
        (simple-iface (decls)
                      (lookup-type-name-in-decls t-name decls))))))

; lookup-qualified-var-in-tenv : sym x sym x tenv -> type
(define lookup-qualified-var-in-tenv
  (lambda (m-name var-name tenv)
    (let ((iface (lookup-module-name-in-tenv tenv m-name)))
      (cases interface iface
        (simple-iface (decls)
                      (lookup-variable-name-in-decls var-name decls))))))

; lookup-type-name-in-tenv : tenv x sym -> type
(define lookup-type-name-in-tenv
  (lambda (tenv name)
    (cases tenvironment tenv
      (empty-tenv () (eopl:error 'lookup-type-name-in-tenv "unbounded ~s" name))
      (extend-tenv (name1 val saved-tenv)
                   (lookup-type-name-in-tenv saved-tenv name))
      (extend-tenv-with-module (name1 m-val saved-tenv)
                               (lookup-type-name-in-tenv saved-tenv name))
      (extend-tenv-with-type (name1 ty saved-tenv)
                             (if (equal? name1 name)
                                 ty
                                 (lookup-type-name-in-tenv saved-tenv name))))))
; lookup-module-name-in-tenv : tenv x sym -> type
(define lookup-module-name-in-tenv
  (lambda (tenv m-name)
    (cases tenvironment tenv
      (empty-tenv () (eopl:error 'lookup-module-name-in-tenv "unbounded ~s" m-name))
      (extend-tenv (name val saved-tenv)
                   (lookup-module-name-in-tenv saved-tenv m-name))
      (extend-tenv-with-module (name m-val saved-tenv)
                               (if (equal? name m-name)
                                   m-val
                                   (lookup-module-name-in-tenv saved-tenv m-name)))
      (extend-tenv-with-type (name1 ty saved-tenv)
                             (lookup-module-name-in-tenv saved-tenv m-name)))))

; lookup-variable-name-in-decls : sym x listof(decl) -> type
(define lookup-variable-name-in-decls
  (lambda (var decls)
    (if (null? decls)
        (eopl:error 'lookup-variable-namae-in-decls "~s not found" var)
        (cases declarition (car decls)
          (val-decl (var1 ty)
                    (if (equal? var1 var)
                        ty
                        (lookup-variable-name-in-decls var (cdr decls))))
          (else (lookup-variable-name-in-decls var (cdr decls)))))))

; lookup-type-name-in-decls : sym x listof(decl) -> type
(define lookup-type-name-in-decls
  (lambda (var decls)
    (if (null? decls)
        (eopl:error 'lookup-type-name-in-decls "~s not found" var)
        (cases declarition (car decls)
          (transparent-type-decl (name ty)
                                 (if (equal? name var)
                                     ty
                                     (lookup-variable-name-in-decls var (cdr decls))))
          (else (lookup-variable-name-in-decls var (cdr decls)))))))



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
                 (append (map type-to-external-form arg-types)
                         (list '->
                               (type-to-external-form result-type))))
      (named-type (name)
                  (list 'named-type
                        name))
      (qualified-type (m-name t-name)
                      (list 'qualified-type
                            m-name
                            t-name)))))

(define report-rator-not-a-proc-type
  (lambda (rator-type rator)
    (eopl:error 'rator-type-error "rator ~s has type ~s" rator rator-type)))

(define external-iface
  (lambda (iface)
    (cases interface iface
      (simple-iface (decls)
                    (map (lambda (decl1)
                           (cases declarition decl1
                             (val-decl (var ty)
                                       (list var
                                             (type-to-external-form ty)))
                             (transparent-type-decl (t-name ty)
                                                    (list 'transparent-decl t-name
                                                          (type-to-external-form ty)))
                             (opaque-type-decl (t-name)
                                               (list 'opaque-decl t-name))))
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
                                             (expand-iface m-name expected-iface tenv)
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

; expand-iface : sym x iface x tenv -> iface
(define expand-iface
  (lambda (m-name iface tenv)
    (cases interface iface
      (simple-iface (decls)
                   (simple-iface (expand-decls m-name decls tenv))))))

; expand-decls : sym x listof(decl) x tenv -> listof(decl)
(define expand-decls
  (lambda (m-name decls internal-tenv)
    (if (null? decls) '()
        (cases declarition (car decls)
          (opaque-type-decl (t-name)
                            (let* ((expanded-type (qualified-type m-name t-name))
                                   (new-env (extend-tenv-with-type t-name expanded-type internal-tenv)))
                              (cons (transparent-type-decl t-name expanded-type)
                                    (expand-decls m-name (cdr decls) new-env))))
          (transparent-type-decl (t-name ty)
                                 (let* ((expanded-type (expand-type ty internal-tenv))
                                        (new-env (extend-tenv-with-type t-name expanded-type internal-tenv)))
                                   (cons (transparent-type-decl t-name expanded-type)
                                         (expand-decls m-name (cdr decls) new-env))))
          (val-decl (var-name ty)
                    (let ((expanded-type (expand-type ty internal-tenv)))
                      (cons (val-decl var-name expanded-type)
                            (expand-decls m-name (cdr decls) internal-tenv))))))))

; interface-of : module-body x tenv -> iface
(define interface-of
  (lambda (m-body tenv)
    (cases module-body m-body
      (defns-module-body (defns)
        (simple-iface (defns-to-decls defns tenv))))))

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
                              (extend-tenv var-name ty tenv)))))
          (type-defn (name ty)
                     (let ((new-env
                           (extend-tenv-with-type
                            name (expand-type ty tenv) tenv)))
                       (cons (transparent-type-decl name ty)
                             (defns-to-decls (cdr defns) new-env))))))))
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
                      (and (<:-decl (car decls1) (car decls2) tenv)
                           (<:-decls (cdr decls1) (cdr decls2)
                                     (extend-tenv-with-decl (car decls1) tenv)))
                      (<:-decls (cdr decls1) decls2
                                (extend-tenv-with-decl (car decls1) tenv))))))))

; <:-decl : decl x decl x tenv -> bool
(define <:-decl
  (lambda (decl1 decl2 tenv)
    (or (and (val-decl? decl1)
             (val-decl? decl2)
             (equiv-type? (decl->type decl1)
                          (decl->type decl2) tenv))
        (and (transparent-type-decl? decl1)
             (transparent-type-decl? decl2)
             (equiv-type? (decl->type decl1)
                          (decl->type decl2) tenv))
        (and (transparent-type-decl? decl1)
             (opaque-type-decl? decl2))
        (and (opaque-type-decl? decl1)
             (opaque-type-decl? decl2)))))

; equiv-type? : type x type x tenv -> bool
(define equiv-type?
  (lambda (ty1 ty2 tenv)
    (equal? (expand-type ty1 tenv)
            (expand-type ty2 tenv))))

; fresh-module-name : sym -> sym
(define fresh-module-name
  (let ((sn -1))
    (set! sn (+ sn 1))
    (lambda (var)
      (string->symbol
       (string-append (symbol->string var)
                      (number->string (+ sn 1)))))))
; extend-tenv-with-decl : decl x tenv -> tenv
(define extend-tenv-with-decl
  (lambda (decl tenv)
    (cases declarition decl
      (val-decl (name ty) tenv)
      (transparent-type-decl (name ty)
                             (extend-tenv-with-type
                              name
                              (expand-type ty tenv)
                              tenv))
      (opaque-type-decl (name)
                        (extend-tenv-with-type
                         name
                         (qualified-type (fresh-module-name '%unknown) name)
                         tenv)))))
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
                 (type-of body (extend-tenv var (expand-type exp1-type tenv) tenv))))
      (proc-exp (vars var-types body)
                (let ((result-type (type-of body
                                            (extend-tenv* vars (map (lambda (x) (expand-type x tenv))
                                                                    var-types)
                                                          tenv))))
                  (proc-type var-types result-type)))
      (call-exp (rator rands)
                (let ((rator-type (type-of rator tenv))
                      (rand-types (map (lambda (x) (type-of x tenv)) rands)))
                  (cases type rator-type
                    (proc-type (arg-types result-type)
                               (begin (check-equal-type! arg-types rand-types rands)
                                      result-type))
                    (else (report-rator-not-a-proc-type rator-type rator)))))
      (letrec-exp (p-result-type p-name b-vars b-var-types p-body letrec-body)
                  (let ((tenv-for-letrec-body
                         (extend-tenv p-name (expand-type (proc-type b-var-types p-result-type) tenv) tenv)))
                    (let ((p-body-type
                           (type-of p-body (extend-tenv* b-vars
                                                         (map (lambda (x) (expand-type x tenv-for-letrec-body)
                                                                tenv-for-letrec-body))
                                                         tenv-for-letrec-body))))
                      (check-equal-type! p-body-type p-result-type p-body)
                      (type-of letrec-body tenv-for-letrec-body))))
      (qualified-var-exp (m-var var1)
                         (lookup-qualified-var-in-tenv m-var var1 tenv))
      )))


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
        (simple-module (defns-to-env defns env))))))

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
                                    (defns-to-env (cdr defns) new-env)))))
          (type-defn (type-name type)
                     (defns-to-env (cdr defns) env))))))

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
      (let-exp (var1 exp1 body)
                (value-of body (extend-env var1
                                           (value-of exp1 env)
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
      (letrec-exp (p-result-type p-name b-var b-var-type p-body letrec-body)
                  (value-of letrec-body
                            (extend-env-rec p-name b-var p-body env)))
      (qualified-var-exp (m-name var1)
                         (lookup-qualified-var-in-env m-name var1 env))
      )))


(define run-val
  (lambda (string)
    (let ((pgm1 (scan&parse string)))
      (type-of-program pgm1)
      (value-of-program pgm1))))

(run-val
 "module tables
   interface [opaque table
              empty : table
              add-to-table : (int int table -> table)
              lookup-in-table : (int table -> int)]
   body
     [type table = (int -> int)
      empty = proc (x : int) -1
      add-to-table = proc (x : int y : int tab : table) 
                        proc (z : int) if zero?(-(x,z)) then y else (tab z)
      lookup-in-table = proc (x : int tab : table) (tab x)]
   let empty = from tables take empty
   in let add-binding = from tables take add-to-table
      in let lookup = from tables take lookup-in-table
         in let table1 = (add-binding 3 300 (add-binding 4 400 (add-binding 3 1000 empty)))
            in -((lookup 3 table1),(lookup 4 table1))")
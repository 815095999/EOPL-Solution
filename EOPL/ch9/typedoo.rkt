#lang eopl
(define identifier? symbol?)
(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    ))

(define the-grammar
  '((program ((arbno class-decl) expression) a-program)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" (arbno identifier "=" expression) "in" expression) let-exp)
    (expression ("proc" "(" (separated-list identifier ":" type ",") ")" expression) proc-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    (expression ("letrec" (arbno type identifier "(" (separated-list identifier ":" type ",") ")" "=" expression)
                          "in" expression) letrec-exp)
    (expression ("begin" expression (arbno ";" expression) "end") begin-exp)
    (expression ("set" identifier "=" expression) assign-exp)
    (expression ("list" "(" expression (arbno "," expression) ")" ) list-exp)
    (class-decl ("class" identifier
                 "extends" identifier
                 (arbno "implements" identifier)
                 (arbno "field" type identifier)
                 (arbno method-decl)) a-class-decl)
    (method-decl ("method" type identifier "("  (separated-list identifier ":" type ",") ")" 
                           expression) a-method-decl)
    (expression ("new" identifier "(" (separated-list expression ",") ")") new-object-exp)
    (expression ("self") self-exp)
    (expression ("send" expression identifier
                        "("  (separated-list expression ",") ")") method-call-exp)
    (expression ("super" identifier "("  (separated-list expression ",") ")") super-call-exp)
    (class-decl ("interface" identifier (arbno abstract-method-decl)) an-interface-decl)
    (abstract-method-decl ("method" type identifier "(" (separated-list identifier ":" type ",") ")") an-abstract-method-decl)
    (expression ("cast" expression identifier) cast-exp)
    (expression ("instanceof" expression identifier) instanceof-exp)
    (type ("int") int-type)
    (type ("bool") bool-type)
    (type ("(" (separated-list type ",") "->" type ")") proc-type)
    (type ("void") void-type)
    (type (identifier) class-type)
    (type ("listof" type) list-type)
    ))

(sllgen:make-define-datatypes the-lexical-spec the-grammar)
(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

; ----------------------------------------------------------------------------------------------
; expval

(define-datatype proc proc?
  (procedure
   (vars (list-of symbol?))
   (body expression?)
   (env environment?)))

(define-datatype expval expval?
  (num-val (value number?))
  (bool-val (boolean boolean?))
  (proc-val (proc proc?))
  (obj-val (obj object?))
  (list-val (lst (list-of expval?))))

(define expval->num
  (lambda (v)
    (cases expval v
      (num-val (num) num)
      (else (expval-extractor-error 'num v)))))

(define expval->bool
  (lambda (v)
    (cases expval v
      (bool-val (bool) bool)
      (else (expval-extractor-error 'bool v)))))

(define expval->proc
  (lambda (v)
    (cases expval v
      (proc-val (proc) proc)
      (else (expval-extractor-error 'proc v)))))

(define expval-extractor-error
  (lambda (variant value)
    (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
                variant value)))


; -------------------------------------------------------------------------------
; reference and store

(define the-store 'uninitialized)

; empty-store : () -> store
(define empty-store
  (lambda () '()))

; initialize-store! : () -> store
; usage: (initialize-store!) sets the-store to the empty-store
(define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))

; get-store : () -> Sto
(define get-store
  (lambda () the-store))

;; reference? : SchemeVal -> Bool
(define reference?
  (lambda (v)
    (integer? v)))

;; newref : ExpVal -> Ref
(define newref
  (lambda (val)
    (let ((next-ref (length the-store)))
      (set! the-store
            (append the-store (list val)))
      next-ref)))

;; deref : Ref -> ExpVal
(define deref
  (lambda (ref)
    (list-ref the-store ref)))

;; setref! : Ref * ExpVal -> Unspecified
(define setref!
  (lambda (ref val)
    (set! the-store
          (letrec
              ((setref-inner
                (lambda (store1 ref1)
                  (cond
                    ((null? store1)
                     (report-invalid-reference ref the-store))
                    ((zero? ref1)
                     (cons val (cdr store1)))
                    (else
                     (cons
                      (car store1)
                      (setref-inner
                       (cdr store1) (- ref1 1))))))))
            (setref-inner the-store ref)))))

(define report-invalid-reference
  (lambda (ref the-store)
    (eopl:error 'setref
                "illegal reference ~s in store ~s"
                ref the-store)))
; --------------------------------------------------------------------------------------
; environment

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (bvars (list-of symbol?))
   (bvals (list-of reference?))
   (saved-env environment?))
  (extend-env-rec**
   (proc-names (list-of symbol?))
   (b-varss (list-of (list-of symbol?)))
   (proc-bodies (list-of expression?))
   (saved-env environment?))
  (extend-env-with-self-and-super
   (self object?)
   (super-name symbol?)
   (saved-env environment?)))

(define init-env
  (lambda () (empty-env)))

(define extend-env1
  (lambda (id val env)
    (extend-env (list id) (list val) env)))

(define apply-env
  (lambda (env search-sym)
    (cases environment env
      (empty-env ()
                 (eopl:error 'apply-env "No binding for ~s" search-sym))
      (extend-env (bvars bvals saved-env)
                  (cond
                    ((location search-sym bvars) => (lambda (n) (list-ref bvals n)))
                    (else (apply-env saved-env search-sym))))
      (extend-env-rec** (p-names b-varss p-bodies saved-env)
                        (cond ((location search-sym p-names)
                               => (lambda (n) (newref (proc-val (procedure
                                                                 (list-ref b-varss n)
                                                                 (list-ref p-bodies n)
                                                                 env)))))
                              (else (apply-env saved-env search-sym))))
      (extend-env-with-self-and-super (self super-name saved-env)
                                      (case search-sym
                                        ((%self) self)
                                        ((%super) super-name)
                                        (else (apply-env saved-env search-sym)))))))

;; location : Sym * Listof(Sym) -> Maybe(Int)
;;   else (location sym syms) = #f
(define location
  (lambda (sym syms)
    (cond
      ((null? syms) #f)
      ((eqv? sym (car syms)) 0)
      ((location sym (cdr syms)) => (lambda (n) (+ n 1)))
      (else #f))))

; -----------------------------------------------------------------------------------
; class and method

;; the-calss-env : classenv
(define the-class-env '())

(define-datatype class class?
  (a-class (super-name (maybe identifier?))
           (field-names (list-of identifier?))
           (method-env method-environment?)))

(define-datatype object object?
  (an-object (class-name identifier?)
             (fields (list-of reference?))))

(define-datatype method method?
  (a-method (vars (list-of identifier?))
            (body expression?)
            (super-name identifier?)
            (field-names (list-of identifier?))))

; selector
(define class->super-name
  (lambda (c-struct)
    (cases class c-struct
	   (a-class (super-name field-names method-env)
		    super-name))))

(define class->field-names
  (lambda (c-struct)
    (cases class c-struct
	   (a-class (super-name field-names method-env)
		    field-names))))

(define class->method-env
  (lambda (c-struct)
    (cases class c-struct
	   (a-class (super-name  field-names method-env)
		    method-env))))


(define object->class-name
  (lambda (obj)
    (cases object obj
	   (an-object (class-name fields)
		      class-name))))

(define object->fields
  (lambda (obj)
    (cases object obj
      (an-object (class-decl fields)
                 fields))))

(define fresh-identifier
  (let ((sn 0))
    (lambda (identifier)
      (set! sn (+ sn 1))
      (string->symbol
       (string-append
        (symbol->string identifier)
        "%"             ; this can't appear in an input identifier
        (number->string sn))))))

; pred
(define maybe
  (lambda (pred)
    (lambda (v)
      (or (not v) (pred v)))))

; a method environment looks like ((method-name method) ...)
(define method-environment?
  (list-of (lambda (p) (and (pair? p)
                            (symbol? (car p))
                            (method? (cadr p))))))


; lookup-class : classname -> class
(define lookup-class
  (lambda (name)
    (let ([maybe-pair (assq name the-class-env)])
      (if maybe-pair
          (cadr maybe-pair)
          (report-unknown-class name)))))

; add-to-class-env! : classname * class -> Unspecified
(define add-to-class-env!
  (lambda (class-name class)
    (set! the-class-env
          (cons (list class-name class)
                the-class-env))))

; initialize-class-env! : listof(classdecl) -> unspecified
(define initialize-class-env!
  (lambda (c-decls)
    (set! the-class-env
          (list
           (list 'object (a-class #f '() '()))))
    (for-each initialize-class-decl! c-decls)))


; initialize-class-decl! : classdecl -> unspecified
(define initialize-class-decl!
  (lambda (c-decl)
    (cases class-decl c-decl
      (a-class-decl (c-name s-name i-names f-types f-names m-decls)
                    (let ([f-names
                           (append-field-names
                            (class->field-names (lookup-class s-name))
                            f-names)])
                      (add-to-class-env!
                       c-name
                       (a-class s-name f-names
                                (merge-method-envs
                                 (class->method-env (lookup-class s-name))
                                 (method-decls->method-env
                                  m-decls s-name f-names))))))
      (an-interface-decl (i-name a-m-decls) #t))))

; method-decls -> method-env
(define method-decls->method-env
  (lambda (m-decls super-name field-names)
    (map
     (lambda (m-decl)
       (cases method-decl m-decl
         (a-method-decl (result-type method-name vars var-types body)
                        (list method-name
                              (a-method vars body super-name field-names)))))
     m-decls)))

; append-field-names :
; listof(FieldName) * Listof(FieldName) -> Listof(FieldName)
(define append-field-names
  (lambda (super-fields new-fields)
    (cond
      [(null? super-fields) new-fields]
      [else
       (cons
        (if (memq (car super-fields) new-fields)
            (fresh-identifier (car super-fields))
            (car super-fields))
        (append-field-names
         (cdr super-fields) new-fields))])))

; merge-method-envs : MethodEnv * MethodEnv -> MethodEnv
(define merge-method-envs
  (lambda (super-m-env new-m-env)
    (append new-m-env super-m-env)))

; find-method : Sym * Sym -> Method
(define find-method
  (lambda (c-name name)
    (let ([m-env (class->method-env (lookup-class c-name))])
      (let ([maybe-pair (assq name m-env)])
        (if (pair? maybe-pair) (cadr maybe-pair)
            (report-method-not-found name))))))

; apply-method : method * obj * listof(expval) -> expval
(define apply-method
  (lambda (m self args)
    (cases method m
      (a-method (vars body super-name field-names)
                (value-of body
                          (extend-env vars (map newref args)
                                      (extend-env-with-self-and-super
                                       self super-name
                                       (extend-env field-names (object->fields self)
                                                   (empty-env)))))))))

; new-object : classname -> obj
(define new-object
  (lambda (class-name)
    (an-object class-name
               (map (lambda (field-name) (newref (list 'uninitialized-field field-name)))
                    (class->field-names (lookup-class class-name))))))

; is-subclass? : classname x classname -> bool
(define is-subclass?
  (lambda (c-name1 c-name2)
    (cond [(equal? c-name1 c-name2) #t]
          [else (let ((s-name (class->super-name
                               (lookup-class c-name1))))
                  (if s-name (is-subclass? s-name c-name2) #f))])))


(define report-unknown-class
  (lambda (name)
    (eopl:error 'lookup-class "Unknown class ~s" name)))


(define report-method-not-found
  (lambda (name)
    (eopl:error 'find-method "unknown method ~s" name)))

; -------------------------------------------------------------
; Evaluator

;; apply-procedure : Proc * Listof(ExpVal) -> ExpVal
(define apply-procedure
    (lambda (proc1 args)
      (cases proc proc1
        (procedure (vars body saved-env)
          (let ((new-env (extend-env vars (map newref args) saved-env)))
            (value-of body new-env))))))

; value-of : exp * env -> expval
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num))
      (var-exp (var) (deref (apply-env env var)))
      (diff-exp (exp1 exp2)
                (let ((val1 (expval->num (value-of exp1 env)))
                      (val2 (expval->num (value-of exp2 env))))
                  (num-val (- val1 val2))))
      (zero?-exp (exp1)
                 (let ((val1 (expval->num (value-of exp1 env))))
                   (if (zero? val1)
                       (bool-val #t)
                       (bool-val #f))))
      (if-exp (exp0 exp1 exp2)
              (if (expval->bool (value-of exp0 env))
                  (value-of exp1 env)
                  (value-of exp2 env)))
      (let-exp (vars exps body)
               (let ((new-env
                      (extend-env vars (map newref (values-of-exps exps env)) env)))
                 (value-of body new-env)))
      (proc-exp (bvars bvar-types body)
                (proc-val
                 (procedure bvars body env)))
      (call-exp (rator rands)
                (let ((proc (expval->proc (value-of rator env)))
                      (args (values-of-exps rands env)))
                  (apply-procedure proc args)))
      (letrec-exp (p-type p-names b-varss b-var-typess p-bodies letrec-body)
                  (value-of letrec-body
                            (extend-env-rec** p-names b-varss p-bodies env)))
      (begin-exp (exp1 exps)
                 (letrec ((value-of-begins
                           (lambda (e1 es)
                             (let ((v1 (value-of e1 env)))
                               (if (null? es)
                                   v1
                                   (value-of-begins (car es) (cdr es)))))))
                   (value-of-begins exp1 exps)))
      (assign-exp (x e)
                  (begin (setref! (apply-env env x)
                                  (value-of e env))
                         (num-val 27)))
      (list-exp (exp1 exps)
                (list-val (cons (value-of exp1 env)
                                (values-of-exps exps env))))
      (self-exp () (apply-env env '%self))
      (method-call-exp (obj-exp method-name rands)
                       (let ((args (values-of-exps rands env))
                             (obj (value-of obj-exp env)))
                         (apply-method
                          (find-method (object->class-name obj) method-name) obj args)))
      (super-call-exp (method-name rands)
                      (let ((args (values-of-exps rands env))
                            (obj (apply-env env '%self)))
                        (apply-method
                         (find-method (apply-env env '%super) method-name) obj args)))
      (new-object-exp (class-name rands)
                      (let ([args (values-of-exps rands env)]
                            [obj (new-object class-name)])
                        (apply-method (find-method class-name 'initialize) obj args)
                        obj))
      (cast-exp (exp c-name)
                (let ([obj (value-of exp env)])
                  (if (is-subclass? (object->class-name obj) c-name)
                      obj
                      (eopl:error 'cast-error "~s is not a type of ~s" obj c-name))))
      (instanceof-exp (exp c-name)
                      (let ([obj (value-of exp env)])
                        (if (is-subclass? (object->class-name obj) c-name)
                            (bool-val #t)
                            (bool-val #f))))
      )))

(define values-of-exps
    (lambda (exps env)
      (map (lambda (exp) (value-of exp env)) exps)))


;; value-of-program : Program -> ExpVal
(define value-of-program
  (lambda (pgm)
    (initialize-store!)
    (cases program pgm
      (a-program (class-decls body)
                 (initialize-class-env! class-decls)
                 (value-of body (init-env))))))

; --------------------------------------------------------------------------------------
; type-environment
(define-datatype type-environment type-environment?
  (empty-tenv)
  (extend-tenv
   (syms (list-of symbol?))
   (vals (list-of type?))
   (tenv type-environment?))
  (extend-tenv-with-self-and-super
   (self type?)
   (super-name symbol?)
   (saved-env type-environment?)))

(define init-tenv
  (lambda () (empty-tenv)))

(define apply-tenv
  (lambda (env search-sym)
    (cases type-environment env
           (empty-tenv ()
                       (eopl:error 'apply-tenv "No type found for ~s" search-sym))
           (extend-tenv (bvars types saved-env)
                        (cond
                         ((location search-sym bvars)
                          => (lambda (n) (list-ref types n)))
                         (else
                          (apply-tenv saved-env search-sym))))
           (extend-tenv-with-self-and-super (self-name super-name saved-env)
                                            (case search-sym
                                              ((%self) self-name)
                                              ((%super) super-name)
                                              (else (apply-tenv saved-env search-sym)))))))

; --------------------------------------------------------------------------------------
; Static Class

(define the-static-class-tenv '())

(define empty-the-static-class-tenv!
  (lambda () (set! the-static-class-tenv '())))

(define add-static-class-binding!
  (lambda (c-name c)
    (set! the-static-class-tenv (cons (list c-name c)
                                      the-static-class-tenv))))

(define-datatype static-class static-class?
  (a-static-class
   (super-name (maybe identifier?))
   (interface-names (list-of identifier?))
   (field-types (list-of type?))
   (field-names (list-of identifier?))
   (method-tenv method-tenv?))
  (an-interface
   (method-tenv method-tenv?)))
(define method-tenv?
  (lambda (menv)
    ((list-of (lambda (x)
                (and (pair? x)
                     (identifier? (car x))
                     (proc-type? (cadr x))))) menv)))
(define proc-type?
  (lambda (p-type)
    (cases type p-type
      (proc-type (arg-types result-type) #t)
      (else #f))))

; initialize-static-class-env! : listof(classdecl) -> unspecified
(define initialize-static-class-env!
  (lambda (c-decls)
    (empty-the-static-class-tenv!)
    (add-static-class-binding! 'object (a-static-class #f '() '() '() '()))
    (for-each add-class-decl-to-static-class-env! c-decls)))

; add-class-decl-to-static-class-env! : classdecl -> unspecified
(define add-class-decl-to-static-class-env!
  (lambda (c-decl)
    (cases class-decl c-decl
      (an-interface-decl (i-name abs-m-decls)
                         (let ([m-tenv (abs-method-decls->method-tenv abs-m-decls)])
                           (check-no-dups! (map car m-tenv) i-name)
                           (add-static-class-binding! i-name (an-interface m-tenv))))
      (a-class-decl (c-name s-name i-names f-types f-names m-decls)
                    (let ([i-names (append (static-class->interface-names (lookup-static-class s-name))
                                           i-names)]
                          [f-names (append-field-names
                                    (static-class->field-names
                                     (lookup-static-class s-name))
                                    f-names)]
                          [f-types (append
                                    (static-class->field-types
                                     (lookup-static-class s-name))
                                    f-types)]
                          [method-tenv (let ([local-method-tenv (method-decls->method-tenv m-decls)])
                                         (check-no-dups! (map car local-method-tenv) c-name)
                                         (merge-method-tenvs (static-class->method-tenv (lookup-static-class s-name))
                                                             local-method-tenv))])
                      (check-no-dups! i-names c-name)
                      (check-no-dups! f-names c-name)
                      (check-for-initialize! method-tenv c-name)
                      (add-static-class-binding! c-name
                                                 (a-static-class s-name i-names f-types f-names method-tenv)))))))

; method-decls -> method-tenv
(define method-decls->method-tenv
  (lambda (m-decls)
    (map
     (lambda (m-decl)
       (cases method-decl m-decl
         (a-method-decl (result-type method-name vars var-types body)
                        (list method-name
                              (proc-type var-types result-type)))))
     m-decls)))
; merge-method-tenvs : menv x menv -> menv
(define merge-method-tenvs
  (lambda (old-menv new-menv)
    (append new-menv old-menv)))

; check-for-initialize! : menv x cname -> unspecified
(define check-for-initialize!
  (lambda (menv cname)
    (cond [(null? menv) (eopl:error 'check-for-initialize! "class ~s has no initializarion" cname)]
          [(equal? (caar menv) 'initialize) #t]
          [check-for-initialize! (cdr menv) cname])))

; check-method-decl! : methoddecl x classname x classname x listof(fieldname) x listof(type)
(define check-method-decl!
  (lambda (m-decl self-name s-name f-names f-types)
    (cases method-decl m-decl
      (a-method-decl (res-type m-name vars var-types body)
                     (let ((tenv (extend-tenv vars var-types
                                              (extend-tenv-with-self-and-super
                                               (class-type self-name) s-name
                                               (extend-tenv f-names f-types (empty-tenv))))))
                       (let ((body-type (type-of body tenv)))
                         (check-is-subtype! body-type res-type m-decl)
                         (if (equal? m-name 'initialize) #t
                             (let ((maybe-super-type (maybe-find-method-type
                                                      (static-class->method-tenv (lookup-static-class s-name)) m-name)))
                               (if maybe-super-type
                                   (check-is-subtype! (proc-type var-types res-type)
                                                      maybe-super-type body)
                                   #t)))))))))

; maybe-find-method-type : menv x mname -> proc-type
(define maybe-find-method-type
  (lambda (m-env m-name)
    (cond [(null? m-env) #f]
          [(equal? (caar m-env) m-name) (cadar m-env)]
          [else (maybe-find-method-type (cdr m-env) m-name)])))
; check-if-implements! : classname x interfacename -> bool
(define check-if-implements!
  (lambda (c-name i-name)
    (cases static-class (lookup-static-class i-name)
      (a-static-class (s-name i-names f-types f-names m-tenv)
                      (eopl:error 'check-if-implements "can't implement non interface ~s to ~s" i-name c-name))
      (an-interface (method-tenv)
                    (let ((class-method-tenv (static-class->method-tenv (lookup-static-class c-name))))
                      (for-each
                       (lambda (method-binding)
                         (let* ((m-name (car method-binding))
                                (m-type (cadr method-binding))
                                (c-method-type (maybe-find-method-type class-method-tenv m-name)))
                           (if c-method-type
                               (check-is-subtype! c-method-type m-type c-name)
                               (eopl:error 'check-if-implements "missing method ~s in class ~s, interface ~s" m-name c-name i-name))))
                       method-tenv))))))


; check-class-decl! : classdecl->unspecified
(define check-class-decl!
  (lambda (c-decl)
    (cases class-decl c-decl
      (an-interface-decl (i-name abs-method-decls) #t)
      (a-class-decl (class-name super-name i-names field-types field-names method-decls)
                    (let ((sc (lookup-static-class class-name)))
                      (for-each
                       (lambda (method-decl)
                         (check-method-decl! method-decl class-name super-name
                                             (static-class->field-names sc)
                                             (static-class->field-types sc)))
                       method-decls))
                    (for-each
                     (lambda (i-name)
                       (check-if-implements! class-name i-name))
                     i-names)))))

; check-no-dups! : listof(identifier) x identifier -> unspecified
(define check-no-dups!
  (lambda (syms c-name)
    (cond [(null? syms) #t]
          [(memv (car syms) (cdr syms))
           (eopl:error 'check-no-dups "find duplicate name ~s in ~s at class ~s" (car syms) syms c-name)]
          [else (check-no-dups! (cdr syms) c-name)])))

; -------------------------------------------------------------
; selector
; abs-method-decls->method-tenv : listof(absmethoddecl) -> method-tenv
(define abs-method-decls->method-tenv
  (lambda (abs-m-decls)
    (map (lambda (abs-m-decl)
           (cases abstract-method-decl abs-m-decl
             (an-abstract-method-decl (result-type m-name arg-ids arg-types)
                                      (list m-name (proc-type arg-types result-type)))))
         abs-m-decls)))

; static-class->interface-names : static-class -> i-name
(define static-class->interface-names
  (lambda (sc)
    (cases static-class sc
      (a-static-class (s-name i-names f-types f-names m-env) i-names)
      (else (eopl:error 'static-class->interface-names "not a static-class ~s" sc)))))
; static-class->field-names : sc -> listof(f-name)
(define static-class->field-names
  (lambda (sc)
    (cases static-class sc
      (a-static-class (s-name i-names f-types f-names m-env) f-names)
      (else (eopl:error 'static-class->field-names "not a static-class ~s" sc)))))

; static-class->field-types : sc -> listof(type)
(define static-class->field-types
  (lambda (sc)
    (cases static-class sc
      (a-static-class (s-name i-names f-types f-names m-env) f-types)
      (else (eopl:error 'static-class->field-types "not a static-class ~s" sc)))))
; static-class->method-tenv : sc -> m-env
(define static-class->method-tenv
  (lambda (sc)
    (cases static-class sc
      (a-static-class (s-name i-names f-types f-names m-env) m-env)
      (an-interface (menv) menv))))
; static-class->super-name : sc -> c-name
(define static-class->super-name
  (lambda (sc)
    (cases static-class sc
      (a-static-class (s-name i-names f-types f-names m-env) s-name)
      (else (eopl:error 'static-class->super-name "not a static-class ~s" sc)))))

; lookup-static-class : sc-name -> sc
(define lookup-static-class
  (lambda (sc)
    (let loop ([m-env the-static-class-tenv])
      (if (null? m-env)
          (eopl:error 'lookup-static-class "unbounded class ~s" sc)
          (if (equal? (caar m-env) sc)
              (cadar m-env)
              (loop (cdr m-env)))))))

; -------------------------------------------------------------
; Type Checker

; type->class-name : type -> c-name
(define type->class-name
  (lambda (ty)
    (cases type ty
      (class-type (name) name)
      (else (eopl:error 'type->class-name "not a class type : ~s" ty)))))
; class-type? : type -> bool
(define class-type?
  (lambda (ty1)
    (cases type ty1
      (class-type (name) #t)
      (else #f))))
; check-equal-type! : type x type x exp -> unspecified
(define check-equal-type!
  (lambda (ty1 ty2 exp)
    (if (not (equal? ty1 ty2))
        (report-unequal-types ty1 ty2 exp)
        #t)))

; report-unequal-types : type x type x exp -> unspecified
(define report-unequal-types
  (lambda (ty1 ty2 exp)
    (eopl:error 'check-equal-type! "Types didn't match: ~s != ~a in ~% ~a" ty1 ty2 exp)))

; exp x tenv -> type
(define type-of
  (lambda (exp tenv)
    (cases expression exp
      (const-exp (num) (int-type))
      (var-exp (var) (apply-tenv tenv var))
      (diff-exp (exp1 exp2)
                (let ((type1 (type-of exp1 tenv))
                      (type2 (type-of exp2 tenv)))
                  (check-equal-type! type1 (int-type) exp1)
                  (check-equal-type! type2 (int-type) exp2)
                  (int-type)))
      (zero?-exp (exp1)
                 (let ((type1 (type-of exp1 tenv)))
                   (check-equal-type! type1 (int-type) exp1)
                   (bool-type)))
      (if-exp (test-exp true-exp false-exp)
              (let ((test-type (type-of test-exp tenv))
                    (true-type (type-of true-exp tenv))
                    (false-type (type-of false-exp tenv)))
                ; these tests either succeed or raise an error
                (check-equal-type! test-type (bool-type) test-exp)
                (check-equal-type! true-type false-type exp)
                true-type))
      (let-exp (ids rands body)
               (let ((new-tenv (extend-tenv ids (types-of-exps rands tenv) tenv)))
                 (type-of body new-tenv)))
      (proc-exp (bvars bvar-types body)
                (let ((result-type
                       (type-of body
                                (extend-tenv bvars bvar-types tenv))))
                  (proc-type bvar-types result-type)))
      (call-exp (rator rands)
                (let ((rator-type (type-of rator tenv))
                      (rand-types  (types-of-exps rands tenv)))
                  (type-of-call rator-type rand-types rands exp)))
      (letrec-exp (proc-result-types proc-names
                                     bvarss bvar-typess proc-bodies
                                     letrec-body)
                  (let ((tenv-for-letrec-body
                         (extend-tenv
                          proc-names
                          (map proc-type bvar-typess proc-result-types)
                          tenv)))
                    (for-each
                     (lambda (proc-result-type bvar-types bvars proc-body)
                       (let ((proc-body-type
                              (type-of proc-body
                                       (extend-tenv
                                        bvars
                                        bvar-types
                                        tenv-for-letrec-body)))) 
                         (check-equal-type!
                          proc-body-type proc-result-type proc-body)))
                     proc-result-types bvar-typess bvarss proc-bodies)
                    (type-of letrec-body tenv-for-letrec-body)))
      (self-exp () (apply-tenv tenv '%self))
      (instanceof-exp (exp class-name)
                      (let ([obj-type (type-of exp tenv)])
                        (if (class-type? obj-type)
                            (bool-type)
                            (eopl:error 'instance-exp "bad type to instanceof ~a in ~a" obj-type exp))))
      (cast-exp (exp class-name)
                (let ([obj-type (type-of exp tenv)])
                  (if (class-type? obj-type)
                      (class-type class-name)
                      (eopl:error 'cast-exp "bad type to cast ~a in ~a" obj-type exp))))
      (method-call-exp (obj-exp method-name rands)
                       (let ([arg-types (types-of-exps rands tenv)]
                             [obj-type (type-of obj-exp tenv)])
                         (type-of-call (find-method-type (type->class-name obj-type) method-name)
                                       arg-types rands exp)))
      (super-call-exp (method-name rands)
                      (let ([arg-types (types-of-exps rands)]
                            [obj-type (apply-tenv tenv '%self)])
                        (type-of-call (find-method-type (apply-tenv tenv '%super) method-name)
                                      arg-types rands exp)))
      (new-object-exp (class-name rands)
                      (let ([arg-types (types-of-exps rands tenv)]
                            [c (lookup-static-class class-name)])
                        (cases static-class c
                          (an-interface (method-tenv)
                                        (eopl:error 'new-object-exp "interface can't instantiate ~s " class-name))
                          (a-static-class (super-name i-names field-types field-names method-tenv)
                                          (type-of-call (find-method-type class-name 'initialize)
                                                        arg-types rands exp)
                                          (class-type class-name)))))
      (begin-exp (exp1 exps)
                 (letrec
                     ((type-of-begins
                       (lambda (e1 es)
                         (let ((v1 (type-of e1 tenv)))
                           (if (null? es)
                               v1
                               (type-of-begins (car es) (cdr es)))))))
                   (type-of-begins exp1 exps)))
      (list-exp (exp1 exps)
                (let ((type-of-car (type-of exp1 tenv)))
                  (for-each
                   (lambda (exp)
                     (check-equal-type!
                      (type-of exp tenv)
                      type-of-car
                      exp))
                   exps)
                  (list-type type-of-car)))
      (assign-exp (id rhs)
                  (check-is-subtype!
                   (type-of rhs tenv)
                   (apply-tenv tenv id)
                   exp)
                  (void-type))
      )))

; find-method-type : c-name x m-name -> proc-type
(define find-method-type
  (lambda (c-name m-name)
    (let ((c (assoc c-name the-static-class-tenv)))
      (if c
          (let ((d (assoc m-name (static-class->method-tenv (cadr c)))))
            (if d
                (cadr d)
                (eopl:error 'find-method-type "unbounded method-name ~s" m-name)))
          (eopl:error 'find-method-type "unbounded class-name : ~s" c-name)))))
; types-of-exps : listof(exp) x tenv -> listof(type)
(define types-of-exps
  (lambda (exps tenv)
    (map (lambda (exp) (type-of exp tenv)) exps)))

; type-of-call : type x listof(type) x listof(exp) x exp -> type
(define type-of-call
  (lambda (rator-type rand-types rands exp)
    (cases type rator-type
      (proc-type (arg-types result-type)
                 (if (not (= (length arg-types) (length rand-types)))
                     (eopl:error 'type-of-call "wrong number of arguments : ~a ~% and ~a ~% in ~a" rand-types rands exp)
                     (begin (for-each check-is-subtype! rand-types arg-types rands)
                            result-type)))
      (else (eopl:error 'type-of-call "rator type not a proc type ~s in ~s" rator-type exp)))))

; check-is-subtype! : type x type x exp -> unspecified
(define check-is-subtype!
  (lambda (ty1 ty2 exp)
    (if (is-subtype? ty1 ty2)
        #t
        (eopl:error 'type-of-call "subtype-check-error! : ~s is not a subtype of ~s" ty1 ty2))))
; is-subtype? : type x type -> bool
(define is-subtype?
  (lambda (ty1 ty2)
    (cases type ty1
      (class-type (name1)
                  (cases type ty2
                    (class-type (name2)
                                (statically-is-subclass? name1 name2))
                    (else #f)))
      (proc-type (args1 res1)
                 (cases type ty2
                   (proc-type (args2 res2)
                              (and (every2? is-subtype? args2 args1)
                                   (is-subtype? res1 res2)))
                   (else #f)))
      (else (equal? ty1 ty2)))))

(define every2?
  (lambda (pred l1 l2)
    (cond [(and (null? l1) (null? l2)) #t]
          [(or (null? l1) (null? l2)) #f]
          [else (and (pred (car l1) (car l2))
                     (every2? pred (cdr l1) (cdr l2)))])))
; statically-is-subclass? : classname x classname -> bool
(define statically-is-subclass?
  (lambda (name1 name2)
    (or (equal? name1 name2)
        (let ((super-name (static-class->super-name (lookup-static-class name1))))
          (if super-name
              (statically-is-subclass? super-name name2)
              #f))
        (let ((interface-names (static-class->interface-names (lookup-static-class name1))))
          (memv name2 interface-names)))))

(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (class-decls exp1)
                 (initialize-static-class-env! class-decls)
                 (for-each check-class-decl! class-decls)
                 (type-of exp1 (init-tenv))))))

(define run
  (lambda (string)
    (let ((pgm (scan&parse string)))
      (eopl:printf "processed type: ~s" (type-of-program pgm))
      (value-of-program pgm))))

(run "
interface tree
    method int sum () 
    method bool equal (t : tree)

class interior-node extends object implements tree
    field tree left 
    field tree right 
    method void initialize(l : tree, r : tree) 
        begin
            set left = l; 
            set right = r end 
    method tree getleft () 
        left 
    method tree getright () 
        right 
    method int sum () 
        -(send left sum(), -(0,send right sum())) 
    method bool equal (t : tree) 
        if instanceof t interior-node 
        then if send left equal(send cast t interior-node getleft())
             then send right equal(send cast t interior-node getright())
             else zero?(1) 
        else zero?(1)

class leaf-node extends object implements tree
    field int value 
    method void initialize (v : int) 
        set value = v 
    method int sum () 
        value 
    method int getvalue () 
        value method 
    bool equal (t : tree) 
        if instanceof t leaf-node 
        then zero?(-(value, send cast t leaf-node getvalue())) 
        else zero?(1)

let o1 = new interior-node ( 
          new interior-node(new leaf-node(3), new leaf-node(4)), 
          new leaf-node(5))
in list(send o1 sum(), if send o1 equal(send o1 getleft()) then 100 else 200)
")


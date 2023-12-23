
#lang racket/base

(require "parse.rkt" "runtime.rkt" (except-in racket/control set)
;        (only-in racket/stream)
         (only-in racket/set seteq set-member? set-add mutable-set set->list)
         racket/mpair
                                        racket/trace
         racket/rerequire racket/match (only-in racket/list remove-duplicates)
         (only-in racket/string string-replace)
         racket/pretty
         parser-tools/lex)

(provide (all-defined-out))
;; (provide gosh-compile simple-binop? semidet-binop? compile-binop new-arg
;;          pprint chunk semidet? det?)

(define stopper "#\\a#\\O#\\_#\\%#\\u0017#\\u0004#\\6#\\u001D#\\u001C#\\;#\\Y#\\S#\\L#\\u0006#\\/#\\c#\\E#\\O#\\newline#\\u0015#\\E#\\D#\\K#\\tab#\\u001A#\\^#\\u0019#\\nul#\\H#\\u001D#\\*#\\$#\\N#\\space#\\T#\\##\\_#\\5#\\D#\\@#\\return#\\I#\\L#\\@#\\*#\\V#\\\\#\\u0005#\\:#\\V#\\Z#\\0#\\G#\\4#\\u0018#\\:#\\page#\\!#\\Z#\\u0016#\\M#\\u0016#\\%#\\u0010#\\%#\\1#\\B#\\u0019#\\4#\\newline#\\?#\\8#\\E#\\u001F#\\W#\\P#\\3#\\@#\\S#\\2#\\S#\\u0002#\\7#\\S#\\!#\\newline#\\[#\\u001F#\\vtab#\\L#\\u001D#\\_#\\$#\\^#\\H#\\5#\\u0006#\\=#\\u001B#\\b")

(define dets (make-parameter #f))
(define semidets (make-parameter #f))
(define chunk (make-parameter 1024))
(define nesting-level (make-parameter 0))
(define pprint (make-parameter #f))
(define next (make-parameter '.gosh-fail))
(define matched (make-parameter #f))
(define in-case? (make-parameter #f))
(define dollar-var-max (make-parameter 0))
(define top-level-vars (make-parameter #f))
(define need-dollar-zero (make-parameter #f))
(define case-match-signal-var (make-parameter #f))
(define app-refs (make-parameter '()))
(define exports (make-parameter #f))
(define imports (make-parameter #f))
(define clause-names (make-parameter #f))
(define module-being-compiled (make-parameter #f))
(define variable-store-constructor (make-parameter
                                    (lambda (name val)
                                      `(set! ,name ,val))))
(define defined-vars (make-parameter '()))

(define (modsyms mod)
  (dynamic-rerequire mod)
  (let-values ([(e ignore) (module->exports mod)])
    (map (lambda (s) (symbol->string (car s))) (cdr (car e)))))

(define (imported? name)
  (and (imports) (hash-ref (imports) name #f)))

(define (setter-name name)
  (if (symbol? name)
      (string->symbol (string-append "@" (symbol->string name)))
      (string-append "@" name)))

(define op-renames (hasheq '> '.gosh->
                           '>= '.gosh->=
                           '< '.gosh-<
                           '<= '.gosh-<=
                           '== '.gosh-==
                           '!= '.gosh-!=
                           '** 'expt))

(define (maybe-rename op)
  (or (hash-ref op-renames op #f) op))

(define simple-binops (seteq '+ '- '* '/ '** '!= '== '> '>= '< '<=
                             '+= '++ 'remainder))

(define semidet-binops (seteq '!= '> '>= '< '<=))

(define special-binops (seteq 'and 'or))

(define (simple-binop? op)
  (set-member? simple-binops op))

(define (semidet-binop? op)
  (set-member? semidet-binops op))

(define (new-arg) (gensym "arg-"))

(define (new-file) (gensym "file-"))

(define (last x)
  (let loop ([l x])
    (if (null? (cdr l))
        (car l)
        (loop (cdr l)))))

(define (compile-dcg desc name pat-in guard exp-in sp ep cont)
  (let* ([pat-and-vars (add-pat-chain-vars pat-in)]
		 [new-exp (apply add-exp-chain-vars exp-in (cdr pat-and-vars))])
	(ppwrap 'XXXXXXXXXXXXXXX (list pat-and-vars new-exp))
	(gcomp `(function-clause (,desc ,name ,(car pat-and-vars), guard #f ,new-exp) ,sp ,ep) cont)))

(define (add-pat-chain-vars pat)
  (define in-var (gensym "in-"))
  (define out-var (gensym "out-"))

  (list (to-pat (if (equal? pat ''())
					(list in-var out-var)
					(append pat (list in-var out-var))))
		in-var out-var))

(define (to-pat p)
  (cond [(equal? p ''()) ''()]
		[(equal? p '()) ''()]
		[else
		 `(or (cons ,(car p) ,(to-pat (cdr p)))
			  (? .force (mcons ,(car p) ,(to-pat (cdr p)))))]))

(define (add-exp-chain-vars exp in out)
  (match exp
	[(list 'and exp1 exp2) (let ([next (gensym "chain-")])
							 `(and ,(add-exp-chain-vars exp1 in next)
								   ,(add-exp-chain-vars exp2 next out)))]
	[(list 'or exp1 exp2) `(or ,(add-exp-chain-vars exp1 in out)
							   ,(add-exp-chain-vars exp2 in out))]
	[(list 'nondcg exp) exp]
	[(list 'terminal val) `(== ,in (list* ,val ,out))]
	[(list 'app name args _) `(app ,name ,(append args (list in out)))]))

(define (compile-unify arg1 arg2 cont)
  (let ([a1 (new-arg)]
        [a2 (new-arg)])
    (gcomp
     arg1
     `(lambda (,a1)
        ,(gcomp
          arg2
          `(lambda (,a2)
			 (.gosh-equal-cont ,a1 ,a2 ,cont)))))))

(define (compile-binop op arg1 arg2 cont)
  (let ([a1 (new-arg)]
        [a2 (new-arg)])
    (gcomp
     arg1
     `(lambda (,a1)
        ,(gcomp
          arg2
          `(lambda (,a2)
             ,(if (semidet-binop? op)
                  (let ([a3 (new-arg)])
                    `(let ([,a3 (,(maybe-rename op) ,a1 ,a2)])
                       (and ,a3 (,cont ,a3))))
                  `(,cont (,(maybe-rename op) ,a1 ,a2)))))))))

(define (compile-xor arg1 arg2 cont)
  (let ([cont-var (gensym "cont-")]
        [success (gensym "success-")]
        [sarg-var (new-arg)])
    `(let ([,cont-var ,cont]
           [,success #f])
       ,(gcomp arg1
               `(lambda (,sarg-var)
                  (set! ,success #t)
                  (,cont-var ,sarg-var)))
       (if ,success
           #f
           ,(gcomp arg2 cont-var)))))

(define (compile-or arg1 arg2 cont)
  (let ([cont-var (gensym "cont-")])
    `(let ([,cont-var ,cont])
       ,(gcomp arg1 cont-var)
       ,(gcomp arg2 cont-var))))

(define (compile-to arg1 arg2 step cont)
  (let ([arg-var1 (new-arg)]
        [arg-var2 (new-arg)]
        [is-char-var (gensym "is-char-")]
        [step-var (gensym "step-")]
        [index (gensym "index-")])
    (if (eq? arg2 '*)
        (gcomp
         arg1
         `(lambda (,arg-var1)
            ,(gcomp
              step
              `(lambda (,step-var)
                 (.iterate* ,arg-var1 ,step-var ,cont)))))
        (gcomp
         arg1
         `(lambda (,arg-var1)
            ,(gcomp
              arg2
              `(lambda (,arg-var2)
                 ,(gcomp
                   step
                   `(lambda (,step-var)
                      (.iterate ,arg-var1 ,arg-var2 ,step-var ,cont))))))))))

(define (compile-and arg1 arg2 cont)
  (let ([a1 (new-arg)])
    (gcomp
     arg1
     `(lambda (,a1) ,(gcomp arg2 cont)))))

(define (compile-* arg cont)
  (let ([count (gensym "count-")]
        [arg-val (new-arg)])
    `(let ([,count 0])
       ,(gcomp arg `(lambda (,arg-val) (set! ,count (add1 ,count))))
       (,cont ,count))))

(define (compile-@* arg cont chunk)
  (let ([c (gensym "cont-")]
        [arg-val (new-arg)])
    (gcomp chunk
           `(lambda (,arg-val)
              (.chunked-lazy-list
               (lambda (,c) ,(gcomp arg c)) ,arg-val ,cont)))))

(define (compile-@ arg cont)
  (let ([c (gensym "cont-")])
    `(.strict-list (lambda (,c) ,(gcomp arg c)) ,cont)))

(define (range start end)
  (let loop ([idx start] [result '()])
    (if (>= idx end)
        (reverse result)
        (loop (add1 idx) (cons idx result)))))

(define (compile-&+ args cont)
  (let ([arg-vals (map (lambda _ (new-arg)) args)]
        [gens (map (lambda _ (gensym "gen-")) args)]
        [vals (map (lambda _ (gensym "val-")) args)]
        [loop (gensym "loop-")])
    `(let (,@(for/list
               [(i (range 0 (length args)))]
               (let ([arg (list-ref arg-vals i)])
                 (list (list-ref gens i)
                       `(generator ()
                                   ,(gcomp (list-ref args i)
                                           `(lambda (,arg)
                                              (yield ,arg)
                                              #f)))))))
       (let ,loop (,@(for/list
                      [(i (range 0 (length args)))]
                      (list (list-ref vals i) (list (list-ref gens i)))))
         (unless (or ,@(for/list
                        [(i (range 0 (length args)))]
                        `(eq? (generator-state ,(list-ref gens i)) 'done)))
                 (,cont (vector ,@(for/list
                                   [(i (range 0 (length args)))]
                                   (list-ref vals i))))
                 (,loop ,@(for/list
                           [(i (range 0 (length args)))]
                           (list (list-ref gens i)))))))))

(define (compile-&++ arg cont)
  (let ([arg-list (new-arg)]
        [generators (gensym "generators-")]
        [gens (gensym "gen-")]
        [gen (gensym "gen-")]
        [res (gensym "res-")]
        [gen-count (gensym "gen-count")]
        [esc (gensym "esc-")]
        [vals (gensym "vals-")]
        [v (gensym "vals-")])
  (gcomp
   arg
   `(lambda (,arg-list)
      (and (or (pair? ,arg-list)
               (mpair? ,arg-list))
           (andmap procedure? ,arg-list)
           (let ([,gen-count (.length (lambda (x) x) ,arg-list)]
                 [,generators
                  (map (lambda (,gen)
                         (generator ()
                                    (,gen (lambda (,res)
                                            (yield ,res)
                                            #f)
                                          '())))
                       ,arg-list)])
             (let loop ([,vals (for/list [(,gen ,generators)] (,gen))])
               (unless (ormap (lambda (,gen)
                                (eq? (generator-state ,gen) 'done))
                              ,generators)
                     (,cont ,vals)
                     (loop (for/list [(,gen ,generators)] (,gen)))))))))))

(define (compile-set-at arg cont)
  (let ([results (gensym "results-")]
        [arg-val (new-arg)])
    `(let ([,results (set)])
       ,(gcomp
         arg
         `(lambda (,arg-val)
            (set! ,results (set-add ,results ,arg-val))))
       (,cont ,results))))

;; (define (compile-set-at arg cont)
;;   (let ([results (gensym "results-")]
;;         [arg-val (new-arg)])
;;     `(let ([,results (set)])
;;        ,(gcomp
;;          arg
;;          `(lambda (,arg-val)
;;             (if (and (set? ,arg-val) (set-empty? ,results))
;;                 (set! ,results ,arg-val)
;;                 (set! ,results (set-add ,results ,arg-val)))))
;;        (,cont ,results))))

(define (compile-hash-at arg cont)
  (let ([arg-val (new-arg)]
        [is-okay? (new-arg)])
    `(let ([|&[%]| (hash)]
           [,is-okay? #t])
       ,(gcomp
         arg
         `(lambda (,arg-val)
            (cond [(association? ,arg-val)
                   (set! |&[%]| (hash-set |&[%]|
                                          (association-key ,arg-val)
                                          (association-val ,arg-val)))]
                  [(hash? ,arg-val)
                   (if (hash-empty? |&[%]|)
                       (set! |&[%]| ,arg-val)
                       (for ([(key val) (in-hash ,arg-val)])
                            (set! |&[%]| (hash-set |&[%]| key val))))]
                  [else (set! ,is-okay? #f)])))
       (and ,is-okay? (,cont |&[%]|)))))

(define (compile-str-at arg cont)
  `(,cont (with-output-to-string (lambda () ,(gcomp arg '.display)))))

(define (compile-once arg cont)
  (if (is-semidet? arg)
      (gcomp arg cont)
      (let ([ec (gensym "escape-")]
            [arg-val (new-arg)])
        `((call/ec
           (lambda (,ec)
             ,(gcomp arg
                     `(lambda (,arg-val)
                        (,ec (lambda () (,cont ,arg-val)))))
             .gosh-fail))))))

(define (list-literal x)
  (match x
    ['() '()]
    [(? (lambda (x) (not (pair? x)))) #f]
    [(cons h t) (let ([car-val (list-literal-value h)]
                      [cdr-val (list-literal t)])
                  (and car-val cdr-val
                       (cons car-val cdr-val)))]))

(define (list-literal-value x)
  (cond [(null? x) '()]
        [(or (var? x) (box? x) (symbol? x)) #f]
        [(not (pair? x)) x]
        [else (match x
                ;; [(and item (or (? symbol?) (? number?) (? string?) (? char?)))
                ;;  item]
                [(list 'atom val) val]
                [(cons 'list val) (list-literal val)]
                [(cons 'tuple val) (tuple-literal val)]
                [_ #f])]))

(define (tuple-literal x)
  (match x
    ['() '#()]
    [(? (lambda (x) (not (pair? x)))) #f]
    [x (let ([vals (map list-literal-value x)])
         (and (andmap (lambda (x) x) vals) (apply vector vals)))]))

(define (compile-tuple args cont)
  (if (null? args)
      `(,cont '#())
      (let ([lval (tuple-literal args)])
        (if lval
            `(,cont ',lval)
            (compile-tuple-tail args '() cont)))))

(define (compile-tuple-tail args so-far cont)
  (let ([arg-val (new-arg)]
        [arg-val2 (new-arg)])
    (cond [(null? args) `(,cont (vector ,@(reverse so-far)))]
          [(or (null? (cdr args)) (pair? (cdr args)))
           (gcomp
            (car args)
            `(lambda (,arg-val)
               ,(compile-tuple-tail
                 (cdr args)
                 (cons arg-val so-far)
                 cont)))]
          [else (error (format "Invalid tuple tail -- ~s" args))])))

(define (compile-list args cont)
  (if (null? args)
      `(,cont '())
      (let ([lval (list-literal args)])
        (if lval
            `(,cont ',lval)
            (compile-list-tail args '() cont)))))

(define (compile-list-tail args so-far cont)
  (let ([arg-val (new-arg)]
        [arg-val2 (new-arg)])
    (cond [(null? args) `(,cont ,(make-mcons-chain so-far))]
          [(or (null? (cdr args)) (pair? (cdr args)))
           (gcomp
            (maybe-translate-parencmd (car args))
            `(lambda (,arg-val)
               ,(compile-list-tail
                 (cdr args)
                 (cons (maybe-splice (car args) arg-val) so-far) cont)))]
          [(gcomp
            (maybe-translate-parencmd (car args))
            `(lambda (,arg-val)
               ,(gcomp
                 (unbox (cdr args))
                 `(lambda (,arg-val2)
                    (unless (or (pair? ,arg-val2)
                                (mpair? ,arg-val2)
                                (null? ,arg-val2)
								(lvar? ,arg-val2))
                      (error (format "Invalid list tail -- ~s"
                                     ,arg-val2)))
                    (,cont ,(make-mcons-chain
                             (cons (maybe-splice (car args) arg-val)
                                   so-far)
                             arg-val2))))))])))

(define (maybe-translate-parencmd arg)
  (match arg
    [(list 'parencmd cmd) `(spliced-parencmd ,cmd)]
    [_ arg]))

(define (maybe-splice exp arg)
  (match exp
    [(list 'parencmd _) (vector arg)]
    [_ arg]))

(define (make-mcons-chain lyst . tail)
  (define (mmc-aux l so-far)
    (cond [(null? l) so-far]
          [(vector? (car l))
           (mmc-aux (cdr l) `(mappend ,(vector-ref (car l) 0) ,so-far))]
          [else (mmc-aux (cdr l) `(.cons ,(car l) ,so-far))]))
  (if (null? tail)
      (mmc-aux lyst ''())
      (mmc-aux lyst (car tail))))

(define (compile-set elements cont)
  (let ([so-far (gensym "so-far-")])
    (if (null? elements)
        `(,cont (set))
        (compile-set-tail elements '(set) cont))))

(define (compile-set-tail elements so-far cont)
  (let ([arg-val (new-arg)]
        [so-far2 (gensym "so-far-")])
    (if (null? elements)
        `(,cont ,so-far)
        (gcomp
         (car elements)
         `(lambda (,arg-val)
            (let ([,so-far2 (set-add ,so-far ,arg-val)])
              ,(compile-set-tail (cdr elements) so-far2 cont)))))))

(define (compile-hash pairs cont)
  (let ([so-far (gensym "so-far-")])
    (if (null? pairs)
        `(,cont (hash))
        (compile-hash-tail pairs '(hash) cont))))

(define (compile-hash-tail pairs so-far cont)
  (let ([arg-val (new-arg)]
        [arg-val2 (new-arg)]
        [so-far2 (gensym "so-far-")])
    (if (null? pairs)
        `(,cont ,so-far)
        (gcomp
         (cadar pairs)
         `(lambda (,arg-val)
            ,(gcomp
              (caddar pairs)
              `(lambda (,arg-val2)
                 (let ([,so-far2 (hash-set ,so-far ,arg-val ,arg-val2)])
                   ,(compile-hash-tail (cdr pairs) so-far2 cont)))))))))

(define (compile-elements-of arg cont)
  (let ([arg-val (new-arg)])
    (gcomp
     arg
     `(lambda (,arg-val) (.dot ,cont ,arg-val)))))

(define (compile-var-aux name cont stringify)
  (update-numeric-var-information-if-appropriate name)
  (cond [(member name (ppwrap 'defined (defined-vars)))
         `(,cont (deref ,(if stringify `(.stringify ,name) name)))]
        [(eq? name '$$)
         `(,cont `(getpid))]
        [(eq? name '$?)
         `(,cont `(get-dollar-q))]
        [else
         `(.look-up-free-var
           ',(string->symbol
              (string-append
               (source-module)
               ".."
               (substring (symbol->string name) 1)))
		   ,stringify ,cont)]))

(define (compile-var name cont)
  (compile-var-aux name cont #f))

(define (compile-if test t e cont)
  (let ([cont-var (gensym "cont-")]
        [arg-val (new-arg)]
        [fail (gensym "fail-")])
    (if e
        `(let ([,cont-var ,cont]
               [,fail #t])
           ,(gcomp
             test
             `(lambda (,arg-val)
                (set! ,fail #f)
                ,(gcomp t cont-var)))
           (if ,fail ,(gcomp e cont-var) #f))
        `(let ([,cont-var ,cont])
           ,(gcomp
             test
             `(lambda (,arg-val) ,(gcomp t cont-var)))))))

(define (compile-match exp pat cont)
  (let ([arg-val (new-arg)])
    (gcomp
     exp
     `(lambda (,arg-val)
        ,(compile-simple-match arg-val pat cont)))))

(define (is-pat-var? item)
  (or (and (symbol? item) (eqv? (string-ref (symbol->string item) 0) #\$))
      (var? item)))

(define (pat-vars pat)
  (define (aux pat)
	(cond [(pair? pat) (append (pat-vars (car pat)) (pat-vars (cdr pat)))]
          [(is-pat-var? pat)
           (if (symbol? pat)
               (list pat)
               (list (var-name pat)))]
          [else '()]))
  (define (nav pat)
	(cond [(set-member? (patvals) pat) (aux pat)]
		  [(pair? pat) (append (nav (car pat)) (nav (cdr pat)))]
		  [else '()]))
  (remove-duplicates (nav pat)))

(define (hash-exp pat)
  (let ([vars (pat-vars pat)])
    (cons 'hash (apply append (map (lambda (v) `(,(strip-$ v) ,v)) vars)))))

(define (compile-simple-match arg pat cont)
  (let* ([arg-val (new-arg)]
         [arg-val2 (new-arg)]
         [bindings (match-up-anon arg-val)])
	(gcomp
     arg
     `(lambda (,arg-val)
        (let ,bindings
          (let ([,arg-val2
                 (match ,arg-val
                   [,(translate-pattern pat) ,(hash-exp pat)]
                   [_ #f])])
            (if ,arg-val2
                (,cont ,arg-val2)
                #f)))))))

(define (compile-match-in arg1 pat arg2 cont)
  (let* ([arg-val (new-arg)]
         [bindings (match-up-anon arg-val)])
	(gcomp
     arg1
     `(lambda (,arg-val)
        (let ,bindings
          (match ,arg-val
            [,(translate-pattern pat)
             ,(parameterize
                  [(defined-vars (append (pat-vars pat) (defined-vars)))]
                (gcomp arg2 cont))]
            [_ #f]))))))

(define (split-at-right lyst count)
  (let loop ([in-list (reverse lyst)] [idx 0] [so-far '()])
    (if (>= idx count)
        (values (reverse in-list) so-far)
        (loop (cdr in-list) (add1 idx) (cons (car in-list) so-far)))))

(define (drop-right lyst count)
  (let loop ([in-list (reverse lyst)] [idx 0])
    (if (>= idx count)
        (reverse in-list)
        (loop (cdr in-list) (add1 idx)))))

(define (translate-pattern pat)
  (match pat
    [(list 'vector head tail)
     `(vector ,(translate-pattern head) ,(translate-pattern tail))]
    [(list 'or
           (list 'cons car cdr)
           (list '? '.force (list 'mcons mcar mcdr)))
     `(or (cons ,(translate-pattern car) ,(translate-pattern cdr))
          (? .force
             (mcons ,(translate-pattern mcar) ,(translate-pattern mcdr))))]
    [(list 'hash-table tail ...)
     (if (equal? (last tail) '...)
         (let-values ([(pats ignore) (split-at-right tail 2)])
           `(hash-table
             ,@(map (lambda (pair) (map translate-pattern pair)) pats)
             ,@ignore))
         `(hash-table
             ,@(map (lambda (pair) (map translate-pattern pair)) tail)))]
    [(list 'and (list '? 'set?)
           (list '? '.to-hash (and ht (cons 'hash-table _))))
     `(and (? set?)
           (app .to-hash ,(translate-pattern ht)))]
    [(? (lambda (x) (and (symbol? x)
                         (eqv? (string-ref (symbol->string x) 0) #\$))))
     pat]
    [(? number?) pat]
    [''ok pat]
    [_ `(app .possibly-stringify ,pat)]))

(define (compile-simple-in arg1 arg2 cont)
  (let* ([arg (new-arg)]
         [bindings (match-up-anon arg)]
         [incode
          (parameterize
           [(nesting-level (add1 (nesting-level)))
            (defined-vars (append (pat-vars arg1) (defined-vars)))]
            (gcomp arg2 cont))])
    (gcomp
     arg1
     `(lambda (,arg) (let ,bindings ,incode)))))

(define (compile-simple-&&> arg1 arg2 cont)
  (let* ([wrapper-arg (new-arg)]
         [arg (new-arg)]
         [bindings (match-up-anon arg)]
         [incode
          (parameterize ([nesting-level (add1 (nesting-level))])
            (gcomp arg2 cont))])
    (gcomp
     arg1
     `(lambda (,wrapper-arg)
        (.rawtail (lambda (,arg) (let ,bindings ,incode)) ,wrapper-arg)))))

(define (compile-simple-||> arg1 arg2 cont)
  (let* ([wrapper-arg (new-arg)]
         [arg (new-arg)]
         [bindings (match-up-anon arg)]
         [incode
          (parameterize ([nesting-level (add1 (nesting-level))])
            `((,cont ,wrapper-arg)
              ,(gcomp arg2 cont)))])
    (gcomp
     arg1
     `(lambda (,wrapper-arg)
        (.rawtail (lambda (,arg) (let ,bindings ,@incode)) ,wrapper-arg)))))

(define (match-up-anon val)
  (let* ([anons
          (for/list ([n (in-range 1 (+ (nesting-level) 2))])
                    (string->symbol
                     (let loop ([str ""] [count n])
                       (if (<= count 0)
                           str
                           (loop (string-append "%" str) (sub1 count))))))]
         [new-anons
          (cons val (drop-right anons 1))])
    (for/list ([old-a anons]
               [new-a new-anons])
              (list old-a new-a))))

(define (compile-seq arg1 arg2 cont)
  `(begin ,(gcomp arg1 '(lambda (x) x))
          ,(gcomp arg2 cont)))

(define (compile-simple-filter exp filt filtexp cont)
  (let* ([is-while (eq? filt 'while)]
         [ec (gensym "escape-")]
         [arg-val (new-arg)]
         [filt-val (new-arg)]
         [bindings (match-up-anon arg-val)]
         [fail (gensym "fail-")]
         [filtcode
          (parameterize
           [(nesting-level (add1 (nesting-level)))
            (defined-vars (append (pat-vars exp) (defined-vars)))]
            `(begin
               ,(gcomp
                 filtexp
                 (if is-while
                     `(lambda (,filt-val)
                        (set! ,fail #f)
                        (,cont ,arg-val))
                     `(lambda (,filt-val)
                        (,cont ,arg-val))))
               ,(if is-while
                    `(if ,fail (,ec #f) (begin (set! ,fail #t) #f))
                    #f)))]
         [expcode
          (parameterize
           [(defined-vars (append (pat-vars exp) (defined-vars)))]
           (if is-while
              `(let ([,fail #t])
                 ,(gcomp exp `(lambda (,arg-val) (let ,bindings ,filtcode))))
              (gcomp exp `(lambda (,arg-val) (let ,bindings ,filtcode)))))])
    (if is-while
        `(call/ec (lambda (,ec) ,expcode))
        expcode)))

(define (compile-match-filter exp pat filt filtexp cont)
  (let* ([is-while (eq? filt 'while)]
         [ec (gensym "escape-")]
         [exp-val (gensym "exp-")]
         [filt-val (gensym "filt-")]
         [bindings (match-up-anon exp-val)]
         [fail (gensym "fail-")]
         [filtcode
          (parameterize
           ([nesting-level (add1 (nesting-level))])
           `(begin
              ,(parameterize
                [(defined-vars (append (pat-vars pat) (defined-vars)))]
                (gcomp
                 filtexp
                 (if is-while
                     `(lambda (,filt-val)
                        (set! ,fail #f)
                        (,cont ,(hash-exp pat)))
                     `(lambda (,filt-val)
                        (,cont ,(hash-exp pat))))))
              ,(if is-while
                   `(if ,fail (,ec #f) (begin (set! ,fail #t) #f))
                   #f)))]
         [expcode
          (parameterize
           [(defined-vars
              (append (pat-vars exp) (pat-vars pat) (defined-vars)))]
           (if is-while
               `(let ([,fail #t])
                  (gcomp
                   exp
                   `(lambda (,exp-val)
                      (let ,bindings
                        (match ,exp-val
                               [,(translate-pattern pat)
                                ,filtcode]
                               [_ #f])))))
               (gcomp
                exp
                `(lambda (,exp-val)
                   (let ,bindings
                     (match ,exp-val
                            [,(translate-pattern pat)
                             ,filtcode]
                            [_ #f]))))))])
    (if is-while
        `(call/ec (lambda (,ec) ,expcode))
        expcode)))

(define (compile-full-post exp pat filt filtexp inexp cont)
  (let* ([is-while (eq? filt 'while)]
         [ec (gensym "escape-")]
         [exp-val (gensym "exp-")]
         [filt-val (gensym "filt-")]
         [bindings (match-up-anon exp-val)]
         [fail (gensym "fail-")]
         [incode
          (parameterize
           [(nesting-level (add1 (nesting-level)))
            (defined-vars (append (pat-vars pat) (defined-vars)))]
            (gcomp inexp cont))]
         [filtcode
          (parameterize [(nesting-level (add1 (nesting-level)))
						 (defined-vars (append (pat-vars pat) (defined-vars)))]
            `(begin
               ,(gcomp
                filtexp
                (if is-while
                    `(lambda (,filt-val)
                       (set! ,fail #f)
                       ,incode)
                    `(lambda (,filt-val)
                       ,incode)))
               ,(if is-while
					`(if ,fail (,ec #f) (begin (set! ,fail #t) #f))
					#f)))]
         [expcode
          (parameterize
           [(defined-vars
              (append (pat-vars exp) (pat-vars pat) (defined-vars)))]
            (if is-while
              `(let ([,fail #t])
                 ,(gcomp
                   exp
                   `(lambda (,exp-val)
                      (let ,bindings
                        (match ,exp-val
                          [,(translate-pattern pat)
                           ,filtcode]
                          [_ #f])))))
              (gcomp
               exp
               `(lambda (,exp-val)
                  (let ,bindings
                    (match ,exp-val
                      [,(translate-pattern pat)
                       ,filtcode]
                      [_ #f]))))))])
    (if is-while
        `(call/ec (lambda (,ec) ,expcode))
        expcode)))

(define (compile-recseq args cont)
  (let* ([oargs (map (lambda (x) `(once ,x)) args)]
         [seqvars (for/list ([i (in-range 1 (length oargs))])
                            (string->symbol
                             (string-append "%" (number->string i))))]
         [bindvars (for/list ([i (in-range 1 (length oargs))])
                             (new-arg))]
         [backexps (drop-right oargs 1)]
         [arg-val (new-arg)]
         [loop (gensym "loop-")]
         [mainexp (gcomp
                   (last args)
                   `(lambda (,arg-val)
                      (,cont ,arg-val)
                      (,loop (add1 %?)
                             ,@(cdr seqvars) ,arg-val)))])
    (letrec ([run-up
              (lambda (exps vars)
                (if (null? exps)
                    `(let ,loop
                       ([%? ,(length backexps)]
                        ,@(for/list ([var seqvars]
                                     [arg bindvars])
                                    (list var arg)))
                       ,mainexp)
                    (let ([exp (car exps)] [var (car vars)])
                      (gcomp exp
                             `(lambda (,var)
                                (,cont ,var)
                                ,(run-up (cdr exps)
                                         (cdr vars)))))))])
      (run-up backexps bindvars))))

(define (compile-! arg cont)
  (let ([ec (gensym "escape-")]
        [arg-val (new-arg)])
    `(call/ec (lambda (,ec)
                ,(gcomp arg `(lambda (,arg-val) (,ec #f)))
                (,cont 'ok)))))

(define (compile-~ arg cont)
  (let ([arg-val (new-arg)])
    (gcomp arg `(lambda (,arg-val) (.wild-match ,arg-val .pwd ,cont)))))

(define (.wmatch arg-val cont)
  (let ([failure #t])
    (.wild-match arg-val .pwd
                 (lambda (arg-val2)
                   (set! failure #f)
                   (cont arg-val2)))
    (and failure
         (cont (.strip-backslashes arg-val)))))

(define (compile-~~ arg cont)
  (let ([av (new-arg)])
    (gcomp arg `(lambda (,av) (.wmatch ,av ,cont)))))

;; (define (compile-~~ arg cont)
;;   (let ([arg-val (new-arg)]
;;         [arg-val2 (new-arg)]
;;         [success (gensym "success-")])
;;     `(let ([,success #f])
;;        ,(gcomp arg
;;                `(lambda (,arg-val)
;;                   (.wild-match ,arg-val .pwd
;;                                (lambda (,arg-val2)
;;                                  (set! ,success #t)
;;                                  (,cont ,arg-val2)))
;;                   (and (not ,success)
;;                        (,cont (.strip-backslashes ,arg-val))))))))

(define (compile-recbind var exp cont)
  (let ([arg-val (new-arg)])
    `(let ([,var #f])
       ,(gcomp exp
               `(lambda (,arg-val)
                  (set! ,var ,arg-val)
                  (,cont ,var))))))

(define (compile-app fun-ref in-args expand-strs cont)
  (define args
    (if expand-strs
        `(list ,@(map (lambda (arg)
                        (if (or (string? arg) (eq? (car arg) 'word-split))
                            `(parencmd (~~ ,arg))
                            arg))
                      (cdr in-args)))
        in-args))
  (match fun-ref
    ;; [(struct var (var-name _))
    ;;  (update-numeric-var-information-if-appropriate var-name)
    ;;  (compile-app-aux var-name args cont)]
    [(list (or 'strexps 'atomexps) _) #:when expand-strs
     (let ([namestr (new-arg)]
           [name (new-arg)])
       (gcomp fun-ref
              `(lambda (,namestr)
                 (.set-up-external-prog-lookup! ,namestr)
                 ,(compile-app-aux
                   `(namespace-variable-value (.fun-name ,namestr))
                   args cont))))]
    [(list 'atom name)
     (app-refs (cons name (app-refs)))
;     (.set-up-external-prog-lookup! name)
     (compile-app-aux (.fun-name name) args cont)]
    [(? string?) #:when expand-strs
     (let ([initial-args (new-arg)]
           [expanded-args (new-arg)]
           [fnamestr (gensym "fun-name-")]
           [fname (gensym "fun-")]
           [cont-val (gensym "cont-")])
       `(let ([,cont-val ,cont])
          ,(gcomp args
                  `(lambda (,initial-args)
                     ,(gcomp `(@ (~~ ,fun-ref))
                             `(lambda (,expanded-args)
                                (let* ([,fnamestr (mcar ,expanded-args)]
                                       [,fname (.fun-name ,fnamestr)])
                                  (.set-up-external-prog-lookup! ,fnamestr)
                                  (if (null? (mcdr ,expanded-args))
                                      ((namespace-variable-value ,fname)
                                       ,cont-val ,initial-args)
                                      ((namespace-variable-value ,fname)
                                       ,cont-val
                                       (mappend (mcdr ,expanded-args)
                                                ,initial-args))))))))))]
    [exp
     (let ([arg-val (new-arg)]
           [arg (new-arg)]
           [lcont (gensym "cont-")])
       (gcomp exp
              `(lambda (,arg-val)
                 (let ([,lcont ,cont])
                   ,(gcomp
                     args
                     `(lambda (,arg)
                        (cond [(procedure? ,arg-val)
                               (,arg-val ,lcont ,arg)]
                              [else (.fetch ,lcont ,arg-val ,arg)])))))))]))

(define (compile-app-aux name args cont)
  (let ([arg-val (new-arg)])
    (gcomp args
           `(lambda (,arg-val)
              (,name ,cont ,arg-val)))))

(define (compile-next args cont)
  (let ([arg-val (new-arg)])
    (gcomp args
           (if (in-case?)
               `(lambda (,arg-val) (,(next) ,arg-val))
               `(lambda (,arg-val) (,(next) ,cont ,arg-val ,(matched)))))))

(define (compile-- arg cont)
  (let ([arg-val (new-arg)])
    (gcomp arg `(lambda (,arg-val) (,cont (- ,arg-val))))))

(define (compile-func-clause-pop namestr cont)
  (define name (string->symbol namestr))
  (let ([gosh-name (string->symbol (string-append ".." namestr))]
        [clause-name-list (hash-ref function-clause-names name)])
    (if (null? (cdr clause-name-list))
        (error "Attempt to pop last function clause.")
        `(begin
           (.pop-clause ',name)
           ,(wrap-clause name
                         (cadr clause-name-list)
                         (cadr clause-name-list)
                         gosh-name
                         #f
                         #f)))))

(define (compile-anon-func namestr pat guard pipe exp cont)
  (let ([arg-vars (pat-vars pat)]
        [cont-var (gensym "cont-")]
        [guard-pass (gensym "guardpass-")]
        [guard-var (gensym "ignore-")])
    (parameterize
     [(defined-vars (append (defined-vars) arg-vars))]
     (if namestr
         (let* ([name (string->symbol namestr)]
                [gosh-name-str (string-append ".." namestr)]
                [gosh-name (string->symbol gosh-name-str)])
           `(let ()
              (define (,gosh-name ,cont-var $*)
                (match $*
                       [,pat
                        ,@(compile-func-guard guard)
                        ,(pipe-compile pipe exp #t cont-var)]
                       [_ #f]))
              (,cont ,gosh-name)))
         (let ([cont-var (gensym "cont-")]
               [guard-pass (gensym "guardpass-")]
               [guard-var (gensym "ignore-")])
           `(,cont
             (lambda (,cont-var $*)
               (match $*
                      [,pat
                       ,@(compile-func-guard guard)
                       ,(pipe-compile pipe exp #t cont-var)]
                      [_ #f]))))))))

(define (fun-str start end)
  (string-replace (substring (current-exp-string)
                             (sub1 (position-offset start))
                             (sub1 (position-offset end)))
                  "\n" " "))

(define (make-bracefun fun-str start end fun-exp)
  (let ([bfun `(bracefun ,(fun-str start end) ,fun-exp)])
    (if (need-dollar-zero)
        `(letrec ([$0 ,bfun]) $0)
        bfun)))

(define (compile-bracefun exp start end cont)
  (define (adjust-op op)
    (cond [(eq? op '**) 'expt]
          [(eq? op '+=) '.addfold]
          [(eq? op '++) '.addcontainerfold]
          [else op]))
  (let ([cont-var (gensym "cont-")])
    (parameterize
        [(dollar-var-max 0)
         (need-dollar-zero #f)]
      (match exp
        [(list '~>
               (and lpat
                    (list 'or (list 'cons _ _)
                          (list '? '.force (list 'mcons _ _)))))
         `(,cont ,(make-bracefun
                   fun-str start end
                   `(lambda (,cont-var $*)
                      ,(gcomp `(post $* (~> ,lpat)) cont-var))))]
        [(list '~> pat)
         `(,cont
           ,(make-bracefun
             fun-str start end
             `(lambda (,cont-var $*)
                ,(gcomp
                  `(post $* (~> ,pat))
                  cont-var))))]
        [(and op (? semidet-binop?))
         `(,cont ,(make-bracefun
                   fun-str start end
                   `(lambda (,cont-var $*)
                      (let ([res (mapply ,(adjust-op op) $*)])
                        (and res (,cont-var res))))))]
        [(and op (? simple-binop?))
         `(,cont ,(make-bracefun
                   fun-str start end
                   `(lambda (,cont-var $*)
                      (,cont-var (mapply ,(adjust-op op) $*)))))]
        [(list 'atom _)
         `(,cont ,(make-bracefun
                   fun-str start end
                   `(lambda (,cont-var $*)
                      ,(gcomp `(app ,exp $* #f) cont-var))))]
        [(list (or 'strexps 'atomexps) _)
         (let ([namestr (new-arg)]
               [name (new-arg)])
           (gcomp
            exp
            `(lambda (,namestr)
               (let ([,name (string->symbol ,namestr)])
                 (.install-shell-lookup ,name)
                 (,cont (namespace-variable-value
                         (.fun-name ,namestr)))))))]
        [_
         (let ([code
                (parameterize
                 [(defined-vars (append (pat-vars exp) (defined-vars)))]
                 (gcomp exp cont-var))])
           (if (> (dollar-var-max) 0)
               `(,cont
                 ,(make-bracefun
                   fun-str start end
                   `(lambda (,cont-var $*)
                      (match $*
                        [,(make-numeric-arglist 1 (dollar-var-max))
                         ,code]
                        [_ #f]))))
               `(,cont ,(make-bracefun
                         fun-str start end
                         `(lambda (,cont-var $*) ,code)))))]))))

(define (make-numeric-arglist current-var max)
  (if (<= current-var max)
      (let ([tail (make-numeric-arglist (add1 current-var) max)]
            [var-symbol (make-numeric-var-symbol current-var)])
        `(or (cons ,var-symbol ,tail)
             (? .force (mcons ,var-symbol ,tail))))
      '_))

(define (make-numeric-var-symbol num)
  (string->symbol (format "$~a" num)))

(define (update-numeric-var-information-if-appropriate name)
  (let* ([name-str (substring (symbol->string name) 1)]
         [is-numeric? (regexp-match #px"^\\d+$" name-str)])
    (when is-numeric?
      (let ([var-num (string->number name-str)])
        (cond [(> var-num (dollar-var-max)) (dollar-var-max var-num)]
              [(= var-num 0) (need-dollar-zero #t)]
              [else #t])))))

(define (compile-case exp clauses cont)
  (let ([arg (new-arg)])
    (if (all-post-match? clauses)
        (gcomp
         exp
         `(lambda (,arg)
            (match
             ,arg
             ,@(compile-post-match-case-clauses clauses cont))))
        (parameterize
         [(case-match-signal-var #f)]
         (gcomp
          exp
          `(lambda (,arg)
             ,@(compile-case-clauses arg (reverse clauses) cont)))))))

(define (compile-post-match-case-clauses clauses cont)
  (match
   clauses
   [(cons (list _ pat guard-wrapper exp) tail)
    (parameterize
     [(defined-vars (append (pat-vars pat) (defined-vars)))]
     (let ([guard (and guard-wrapper (cadr guard-wrapper))])
       (cons `[,pat
               ,@(compile-func-guard guard)
               ,(gcomp exp cont)]
             (compile-post-match-case-clauses tail cont))))]
    [x '()]))

(define (all-post-match? clauses)
  (andmap (lambda (c) (eq? (car c) '>~)) clauses))

(define (compile-case-clauses arg clauses cont)
  (match clauses
    [(cons (list discriminator pat guard-wrapper exp) tail)
    (parameterize
     [(defined-vars (append (pat-vars pat) (defined-vars)))]
     (let ([guard (and guard-wrapper (cadr guard-wrapper))])
       (case discriminator
         [(<!)
          `((match ,arg
              [,pat
               ,@(compile-func-guard guard)
               ,@(maybe-signal-match)
               ,(gcomp exp cont)]
              [_ #f])
            ,@(compile-case-clauses arg tail cont))]
         [(=!)
          (let* ([fname (gensym "fun-")]
                 [next-arg (new-arg)]
                 [clauses (compile-case-clauses next-arg tail cont)])
            `((let ([,fname
                     (lambda (,next-arg)
                       ,@(if (null? clauses)
                             '(#f)
                             clauses))])
                (match ,arg
                  [,pat
                   ,@(compile-func-guard guard)
                   ,@(maybe-signal-match)
                   ,(parameterize [(next fname) (in-case? #t)]
                      (gcomp exp cont))]
                  [_ (,fname ,arg)]))))]
         [(>!)
          `(,@(compile-case-clauses arg tail cont)
            (match ,arg
              [,pat
               ,@(compile-func-guard guard)
               ,@(maybe-signal-match)
               ,(gcomp exp cont)]
              [_ #f]))]
         [(<?)
          (let ([success (gensym "success-")]
                [sarg-var (new-arg)])
            `((let ([,success #f])
                (match ,arg
                  [,pat
                   ,@(compile-func-guard guard)
                   ,@(maybe-signal-match)
                   ,(gcomp exp
                           `(lambda (,sarg-var)
                              (set! ,success #t)
                              (,cont ,sarg-var)))]
                  [_ #f])
                (if ,success
                    #f
                    (begin ,@(compile-case-clauses arg tail cont))))))]
         [(>?)
          (let ([success (gensym "success-")]
                [sarg-var (new-arg)])
            `((let ([,success #f])
                ,@(compile-case-clauses arg tail `(lambda (,sarg-var)
                                                    (set! ,success #t)
                                                    (,cont ,sarg-var)))
                (if ,success
                    #f
                    (match ,arg
                      [,pat
                       ,@(compile-func-guard guard)
                       ,@(maybe-signal-match)
                       ,(gcomp exp cont)]
                      [_ #f])))))]
         [(>~)
          (if (case-match-signal-var)
              `(,@(compile-case-clauses arg tail cont)
                (if ,(case-match-signal-var)
                    #f
                    (match ,arg
                      [,pat
                       ,@(compile-func-guard guard)
                       ,@(maybe-signal-match)
                       ,(gcomp exp cont)]
                      [_ #f])))
              (parameterize
                  [(case-match-signal-var (gensym "matched-"))]
                `((let ([,(case-match-signal-var) #f])
                    ,@(compile-case-clauses arg tail cont)
                    (if ,(case-match-signal-var)
                        #f
                        (match ,arg
                          [,pat
                           ,@(compile-func-guard guard)
                           ,@(maybe-signal-match)
                           ,(gcomp exp cont)]
                          [_ #f]))))))])))]
    [x '()]))

(define (maybe-signal-match)
  (let ([match-var (case-match-signal-var)])
    (if match-var
        `((set! ,match-var #t))
        '())))

(define (make-patch-fun prev-var-name name load-time-prev)
  (let ([prev-names (hash-ref function-clause-names name #f)]
        [arg-name (new-arg)])
    (if prev-names
        #f
        `(lambda ,arg-name
           (set! ,prev-var-name ,load-time-prev)
           (apply ,prev-var-name ,arg-name)))))

(define (wrap-clause name clause-name clause gosh-name start end)
  (clause-names (cons clause-name (clause-names)))
  (let ([cont-arg (new-arg)]
        [cont-var (new-arg)]
        [level-var (gensym "level-")]
        [level-fun (gensym "level-fun-")]
        [wrapper-var (new-arg)])
    `(begin
       (set! ,clause-name ,clause)
       (.define-clause-wrapper ',name ',clause-name ,clause
                               ',gosh-name
                               ,(and start
                                     end
                                     (substring
                                      (current-exp-string)
                                      (sub1 (position-offset start))
                                      (sub1 (position-offset end))))))))

    ;; `(.define-clause-wrapper ',name ',clause-name ,clause
    ;;                          ',gosh-name
    ;;                          ,(and start
    ;;                                end
    ;;                                (substring (current-exp-string)
    ;;                                           (sub1 (position-offset start))
    ;;                                           (sub1 (position-offset end)))))))

(define *undefined* (list 'undefined))

(define (interactive-setter gosh-name)
  (if (or (module-name)
          (not (eq? (namespace-variable-value (setter-name gosh-name) #t
                                              (lambda () *undefined*))
                    *undefined*)))
      '()
      `((define (,(setter-name gosh-name) fun)
          (set! ,gosh-name fun)))))

(define (subexp start end)
  (substring (current-exp-string)
             (sub1 (position-offset start))
             (sub1 (position-offset end))))

(define (chunks spans)
;;  spans)
  (map (lambda (x)
         (substring (current-exp-string)
                    (sub1 (position-offset (car x)))
                    (sub1 (position-offset (cadr x)))))
       spans))

(define (source-module)
  (or (module-name) "<toplevel>"))

(define (compile-func-clause discriminator namestr pat guard pipe exp
                             start end cont)
  (define name (string->symbol namestr))
  (app-refs (cons namestr (app-refs)))
  (let* ([gosh-name-str (string-append ".." namestr)]
         [gosh-name (string->symbol gosh-name-str)]
         [clause-name (gensym (string-append gosh-name-str "-"))]
		 [.trail-list '()]
		 [.trail (lambda (x y) (set! .trail-list (cons (list x y) .trail-list)))]
		 [.untrail (lambda () (for [(item .trail-list)]
								   (if (procedure? (cadr item))
									   (remove-constraint! (car item) (cadr item))
									   (unbind! (car item)))))]
         [prev-var (gensym "prev-")]
         [prev-funobj (gensym "prev-funobj-")]
         [cont-var (gensym "cont-")]
         [matched-var (gensym "matched-")]
         [guard-pass (gensym "guardpass-")]
         [guard-var (gensym "ignore-")]
         [clause (gensym "clause-")])
    (parameterize
     [(defined-vars
        (append (pat-vars pat) (pat-vars pipe) (pat-vars exp) (defined-vars)))]
     (when (exports)
           (exports (set-add (exports) gosh-name)))
     (case discriminator
       [(<!)
        ;; first reference to named function creates command lookup
        `(begin
           ,@(interactive-setter gosh-name)
           (,(setter-name gosh-name)
            (let ([,prev-funobj ,gosh-name]
                  [,prev-var (get-fun ,gosh-name)])
              (let ([,clause
                     (lambda (,cont-var $* ,matched-var)
                       (match $*
                              [,pat
                               ,@(compile-func-guard guard)
                               (when ,matched-var (vector-set! ,matched-var 0 #t))
                               ,(pipe-compile pipe exp #f cont-var)]
                              [_ #f])
					   (.untrail)
                       (,prev-var ,cont-var $* ,matched-var))])
                                        ;             (init-clause-name ',clause-name)
                                        ;             (set-func! ',clause-name ,clause)
                ,(wrap-clause name clause-name clause gosh-name start end)
                (goshfun ,clause (get-defs ,prev-funobj
                                           ,(source-module)
                                           ,(subexp start end))
                         ,namestr ',gosh-name))))
           (,cont (if (.loading) (void) ,namestr)))]
       [(=!)
        (parameterize
         [(next prev-var) (matched matched-var)]
         (let ([cont-var (gensym "cont-")])
           `(begin
              ,@(interactive-setter gosh-name)
              (,(setter-name gosh-name)
               (let ([,prev-funobj ,gosh-name]
                     [,prev-var (get-fun ,gosh-name)])
                 (let ([,clause
                        (lambda (,cont-var $* ,matched-var)
                          (match $*
                                 [,pat
                                  ,@(compile-func-guard guard)
                                  (when ,matched-var (vector-set! ,matched-var 0 #t))
                                  ,(pipe-compile pipe exp #t cont-var)]
                                 [_ (,prev-var ,cont-var $* ,matched-var)]))])
                                        ;                 (init-clause-name ',clause-name)
                                        ;                 (set-func! ',clause-name ,clause)
                   ,(wrap-clause name clause-name clause gosh-name start end)
                   (goshfun ,clause (get-defs ,prev-funobj
                                              ,(source-module)
                                              ,(subexp start end))
                            ,namestr ',gosh-name))))
              (,cont (if (.loading) (void) ,namestr)))))]
       [(>!)
        `(begin
           ,@(interactive-setter gosh-name)
           (,(setter-name gosh-name)
            (let ([,prev-funobj ,gosh-name]
                  [,prev-var (get-fun ,gosh-name)])
              (let ([,clause
                     (lambda (,cont-var $* ,matched-var)
                       (,prev-var ,cont-var $* ,matched-var)
                       (match $*
                              [,pat
                               ,@(compile-func-guard guard)
                               (when ,matched-var (vector-set! ,matched-var 0 #t))
                               ,(pipe-compile pipe exp #f cont-var)]
                              [_ #f]))])
                                        ;             (init-clause-name ',clause-name)
                                        ;             (set-func! ',clause-name ,clause)
                ,(wrap-clause name clause-name clause gosh-name start end)
                (goshfun ,clause (get-defs ,prev-funobj
                                           ,(source-module)
                                           ,(subexp start end))
                         ,namestr ',gosh-name))))
           (,cont (if (.loading) (void) ,namestr)))]
       [(<?)
        (let ([success (gensym "success-")]
              [sarg-var (new-arg)])
          `(begin
             ,@(interactive-setter gosh-name)
             (,(setter-name gosh-name)
              (let ([,prev-funobj ,gosh-name]
                    [,prev-var (get-fun ,gosh-name)])
                (let ([,clause
                       (lambda (,cont-var $* ,matched-var)
                         (let ([,success #f])
                           (match $*
                                  [,pat
                                   ,@(compile-func-guard guard)
                                   (when ,matched-var (vector-set! ,matched-var 0 #t))
                                   ,(pipe-override-compile pipe exp success
                                                           sarg-var cont-var)]
                                  [_ #f])
                           (if ,success
                               #f
                               (,prev-var ,cont-var $* ,matched-var))))])
                                        ;               (init-clause-name ',clause-name)
                                        ;               (set-func! ',clause-name ,clause)
                  ,(wrap-clause name clause-name clause gosh-name start end)
                  (goshfun ,clause (get-defs ,prev-funobj
                                             ,(source-module)
                                             ,(subexp start end))
                           ,namestr ',gosh-name))))
             (,cont (if (.loading) (void) ,namestr))))]
       [(>?)
        (let ([success (gensym "success-")]
              [sarg-var (new-arg)])
          `(begin
             ,@(interactive-setter gosh-name)
             (,(setter-name gosh-name)
              (let ([,prev-funobj ,gosh-name]
                    [,prev-var (get-fun ,gosh-name)])
                (let ([,clause
                       (lambda (,cont-var $* ,matched-var)
                         (let ([,success #f])
                           (,prev-var
                            (lambda (,sarg-var)
                              (set! ,success #t)
                              (,cont-var ,sarg-var))
                            $*
                            ,matched-var)
                           (if ,success
                               #f
                               (match $*
                                      [,pat
                                       ,@(compile-func-guard guard)
                                       (when ,matched-var
                                             (vector-set! ,matched-var 0 #t))
                                       ,(pipe-compile pipe exp #f cont-var)]
                                      [_ #f]))))])
                                        ;               (init-clause-name ',clause-name)
                                        ;               (set-func! ',clause-name ,clause)
                  ,(wrap-clause name clause-name clause gosh-name start end)
                  (goshfun ,clause (get-defs ,prev-funobj
                                             ,(source-module)
                                             ,(subexp start end))
                           ,namestr ',gosh-name))))
             (,cont (if (.loading) (void) ,namestr))))]
       [(>~)
        `(begin
           ,@(interactive-setter gosh-name)
           (,(setter-name gosh-name)
            (let ([,prev-funobj ,gosh-name]
                  [,prev-var (get-fun ,gosh-name)])
              (let ([,clause
                     (lambda (,cont-var $* ,matched-var)
                       (unless ,matched-var (set! ,matched-var (vector #f)))
                       (,prev-var
                        ,cont-var
                        $*
                        ,matched-var)
                       (if (vector-ref ,matched-var 0)
                           #f
                           (match $*
                                  [,pat
                                   ,@(compile-func-guard guard)
                                   (vector-set! ,matched-var 0 #t)
                                   ,(pipe-compile pipe exp #f cont-var)]
                                  [_ #f])))])
                ,(wrap-clause name clause-name clause gosh-name start end)
                (goshfun ,clause (get-defs ,prev-funobj
                                           ,(source-module)
                                           ,(subexp start end))
                         ,namestr ',gosh-name))))
           (,cont (if (.loading) (void) ,namestr)))]))))

(define (pipe-override-compile pipe exp success sarg-var cont-var)
  (if pipe
      (compile-pipe-list exp pipe #f `(lambda (,sarg-var)
                                        (set! ,success #t)
                                        (,cont-var ,sarg-var)))
      (gcomp exp
             `(lambda (,sarg-var)
                (set! ,success #t)
                (,cont-var ,sarg-var)))))

(define (pipe-compile pipe exp is-bottom cont-var)
  (if pipe
      (compile-pipe-list exp pipe is-bottom cont-var)
      (gcomp exp cont-var)))

(define (compile-pipe-list arg pat is-bottom cont)
  (let* ([is-up #f]
         [pipelist (new-arg)]
         [bindings (match-up-anon pipelist)])
    (match pat
           [(list 'up val)
            (set! pat (cadr pat))
            (set! is-up #t)]
           [_ 'ok])
    (if is-bottom
        (if is-up
            `(if (thread-cell-ref .semidetapp)
                 (.sendin
                  (lambda (,pipelist)
                    (let ,bindings
                      ,(if (eq? pat #t)
                           (gcomp arg cont)
                           `(match ,pipelist
                                   [,(translate-pattern pat) ,(gcomp arg cont)]
                                   [_ #f])))))
                 (let ([,pipelist (thread-cell-ref .pipelist)])
                   (unless
                     ,pipelist
                     (set! ,pipelist (.pipe-list ,(chunk))))
                   (.dot (lambda (,pipelist)
                           (let ,bindings
                             ,(if (eq? pat #t)
                                  (gcomp arg cont)
                                  `(match ,pipelist
                                          [,(translate-pattern pat)
                                           ,(gcomp arg cont)]
                                          [_ #f]))))
                         ,pipelist)))
            `(let ([,pipelist (thread-cell-ref .pipelist)])
                    (unless
                     ,pipelist
                     (set! ,pipelist (.pipe-list ,(chunk))))
                    (let ,bindings
                      ,(if (eq? pat #t)
                           (gcomp arg cont)
                           `(match ,pipelist
                                   [,(translate-pattern pat) ,(gcomp arg cont)]
                                   [_ #f])))))
        `(let ([,pipelist (thread-cell-ref .pipelist)])
           (unless
            ,pipelist
            (set! ,pipelist (.pipe-list ,(chunk))))
           ,(if is-up
                `(.dot (lambda (,pipelist)
                         (let ,bindings
                           ,(if (eq? pat #t)
                                (gcomp arg cont)
                                `(match ,pipelist
                                        [,(translate-pattern pat)
                                         ,(gcomp arg cont)]
                                        [_ #f]))))
                       ,pipelist)
                `(let ,bindings
                   ,(if (eq? pat #t)
                        (gcomp arg cont)
                        `(match ,pipelist
                                [,(translate-pattern pat) ,(gcomp arg cont)]
                                [_ #f]))))))))

(define (compile-func-guard guard)
  (if guard
      (let ([guard-pass (gensym "guardpass-")]
            [guard-var (gensym "ignore-")])
        `(#:when (let ([,guard-pass #f])
                   ,(gcomp guard
                           `(lambda (,guard-var)
                              (set! ,guard-pass #t)))
                   ,guard-pass)))
      '()))

(define (compile-fetch table key cont)
  (let ([arg-val (new-arg)]
        [arg-val2 (new-arg)]
        [hash-val (gensym "hash-")])
    (gcomp
     table
     `(lambda (,arg-val)
        ,(gcomp
          key
          `(lambda (,arg-val2)
             (.fetch ,cont ,arg-val ,arg-val2)))))))

(define (compile-assoc left right cont)
  (let ([arg-val (new-arg)]
        [arg-val2 (new-arg)])
    (gcomp left
           `(lambda (,arg-val)
              ,(gcomp right
                      `(lambda (,arg-val2)
                         (,cont (association ,arg-val ,arg-val2))))))))

(define (compile-:= container arglist item cont)
  (let ([cont-val (new-arg)]
        [args (new-arg)]
        [item-val (new-arg)])
    (gcomp container
           `(lambda (,cont-val)
              ,(gcomp
                  arglist
                  `(lambda (,args)
                     ,(gcomp
                       item
                       `(lambda (,item-val)
                          (.assign ,cont ,cont-val ,args ,item-val)))))))))

(define (compile--= container item cont)
  (let ([arg-val (new-arg)]
        [arg-val2 (new-arg)])
    (gcomp container
           `(lambda (,arg-val)
              ,(gcomp item
                      `(lambda (,arg-val2)
                         (.remove ,cont ,arg-val ,arg-val2)))))))

(define (compile-+= container item cont)
  (let ([arg-val (new-arg)]
        [arg-val2 (new-arg)])
    (gcomp container
           `(lambda (,arg-val)
              ,(gcomp item
                      `(lambda (,arg-val2)
                         (,cont (.add ,arg-val ,arg-val2))))))))

(define (compile-++ container item cont)
  (let ([arg-val (new-arg)]
        [arg-val2 (new-arg)])
    (gcomp container
           `(lambda (,arg-val)
              ,(gcomp item
                      `(lambda (,arg-val2)
                         (,cont (.addcontainer ,arg-val ,arg-val2))))))))

(define (compile-// goal solution-number cont)
  (let ([count (gensym "count-")]
        [arg-val (new-arg)]
        [num (new-arg)])
    `(let ([,count 0])
       ,(gcomp solution-number
               `(lambda (,num)
                  (and (exact-nonnegative-integer? ,num)
                        ,(gcomp goal
                                `(lambda (,arg-val)
                                   (if (>= ,count ,num)
                                       (,cont ,arg-val)
                                       (set! ,count (add1 ,count)))))))))))

(define (compile-//* goal cont)
  (let ([succeeded? (gensym "success-")]
        [arg-val (new-arg)]
        [last-val (new-arg)])
    `(let ([,succeeded? #f]
           [,last-val #f])
       ,(gcomp goal
               `(lambda (,arg-val)
                  (set! ,succeeded? #t)
                  (set! ,last-val ,arg-val)))
       (and ,succeeded? (,cont ,last-val)))))

(define (compile-assignment var val cont)
  (let ([arg (new-arg)]
                                        ;        [varname (string->symbol (string-append "$" var))])
        [varname (string->symbol var)]
        [modvarname (string->symbol
                     (string-append (source-module) ".." var))])
;    (set-add! (top-level-vars) varname)
    (gcomp `(once ,val)
           `(lambda (,arg)
;              (namespace-set-variable-value! ',varname ,arg)
;              (set! ,varname ,arg)
              ;; parameterize so tests can access vars that have been set
              ;; dynamically
              (if (hash-ref (.env) ',varname #f)
                  (hash-set! (.env) ',varname ,arg)
                  (hash-set! (.free-vars) ',modvarname ,arg))
              (,cont (void))))))

(define (compile-&&. cmd othercmd cont)
  `(parameterize
    [(.cmd-success #t)]
    (begin ,(gcomp cmd cont)
           (when (.cmd-success) ,(gcomp othercmd cont)))))

(define (compile-||. cmd othercmd cont)
  (let ([ec (gensym "ec-")])
    `(parameterize
      [(.cmd-success #t)]
      (begin (call/ec
              (lambda (,ec)
                (parameterize
                 [(.throw-to-or. ,ec)]
                 (with-handlers
                  ([exn?
                    (lambda (err)
                      (fprintf (current-error-port)
                               "Error: ~a~%"
                               (exn-message err))
                      (.cmd-success #f)
                      (set-code-set! #t)
                      (set-dollar-q 1)
                      #f)])
                  ,(gcomp cmd cont))
                 (unless (.cmd-success)
                         (.cmd-success #t)
                         ,(gcomp othercmd cont)))))))))

(define (is-semidet-app exp)
  (match exp
         [(list 'app _ e _) (semidet? e)]
         [_ #f]))

(define (compile-pipe item otherpipe err cont)
  (let ([chan (gensym "chan-")]
        [prev-thread (gensym "thread-")]
        [arg-val (new-arg)]
        [cmd-success (gensym "cmd-success-")]
        [in (gensym "in-")]
        [out (gensym "out-")]
        [err-thread (gensym "thread-")])
    `(let* ([,chan (make-async-channel 2048)]
            [,prev-thread (current-thread)]
            [,cmd-success #t])
       (thread
        (lambda ()
          (with-handlers
              ([exn?
                (lambda (err) (fprintf (current-error-port)
                                       "Error: ~a~%"
                                       (exn-message err)))])
              (thread-cell-set! .stdin ,chan)
              ,(if (is-semidet-app otherpipe)
                   `(begin (thread-cell-set! .semidetapp #t)
                           ,(gcomp otherpipe cont))
                   (gcomp otherpipe cont)))
          (set! ,cmd-success (.cmd-success))
          (thread-send ,prev-thread 'ok)))
       ,(if err
            `(let-values
              ([(,in ,out) (make-pipe)])
              (let ([,err-thread
                     (thread
                      (lambda ()
                        (let loop ([line (read-line ,in)])
                          (unless (equal? line stopper)
                                  (async-channel-put ,chan line)
                                  (loop (read-line ,in))))))])
                (parameterize
                 [(current-error-port ,out)]
                 ,(gcomp
                   item
                   `(lambda (,arg-val)
                      (async-channel-put ,chan ,arg-val))))
                (fprintf ,out "~a~%" stopper)
                (thread-wait ,err-thread)))
            (gcomp
             item
             `(lambda (,arg-val)
                (async-channel-put ,chan ,arg-val))))
       (async-channel-put ,chan .channel-empty)
       (thread-receive)
       (.cmd-success ,cmd-success)
       #f)))

(define (compile-file-input exp cont)
  (let ([arg-val (new-arg)]
        [file-arg-val (new-arg)]
        [inport (new-file)])
    (gcomp exp
           `(lambda (,file-arg-val)
              (when (symbol? ,file-arg-val)
                    (set! ,file-arg-val (symbol->string ,file-arg-val)))
              (call-with-input-file ,file-arg-val
                (lambda (,inport)
                  (let loop ([line (read-line ,inport)])
                    (unless (eof-object? line)
                            (,cont line)
                            (loop (read-line ,inport))))))))))


(define (compile-redirect source desc mode outfileexp cont)
  (let* ([arg-val (new-arg)]
         [file-arg-val (new-arg)]
         [body (gcomp source
                      `(lambda (,arg-val)
                         (if (string? ,arg-val)
                             (printf "~a" ,arg-val)
                             (.gosh-print ,arg-val))
                         (newline)))])
    (gcomp outfileexp
           `(lambda (,file-arg-val)
              (when (symbol? ,file-arg-val)
                    (set! ,file-arg-val (symbol->string ,file-arg-val)))
              ,(case desc
                [(both)
                 `(with-output-to-file ,file-arg-val
                    (lambda ()
                     (parameterize
                      [(current-error-port (current-output-port))]
                      ,body))
                    #:exists ',mode)]
                [(1) `(with-output-to-file ,file-arg-val
                        (lambda () ,body) #:exists ',mode)])))))

              ;; (call-with-output-file ,file-arg-val
              ;;   (lambda (,outport)
              ;;     ,(gcomp source
              ;;             `(lambda (,arg-val)
              ;;                (if (string? ,arg-val)
              ;;                    (fprintf ,outport "~a" ,arg-val)
              ;;                    (.gosh-fprint ,outport ,arg-val))
              ;;                (newline ,outport))))
              ;;   #:exists ',mode)))))

(define (compile-str exps cont)
  (compile-str-aux exps cont '()))

(define (compile-str-aux exps cont sofar)
  (if (null? exps)
      (if (= (length sofar) 1)
          `(,cont ,@sofar)
          `(,cont (string-append ,@(reverse sofar))))
      (let [(arg (new-arg))]
        (compile-str-arg
         (car exps)
         `(lambda (,arg)
           ,(compile-str-aux (cdr exps) cont (cons arg sofar)))))))

(define (compile-str-arg exp cont)
  (cond [(string? exp) `(,cont ,exp)]
        [(eq? (car exp) 'var)
         (compile-var-aux (cadr exp) cont #t)]
        [else
         (let ([arg (new-arg)])
           (if (eq? (car exp) 'bracket)
               (gcomp (cadr exp)
                      `(lambda (,arg) (,cont (.stringify ,arg))))
               (gcomp `(@ ,(cadr exp))
                      `(lambda (,arg) (,cont (flatlist ,arg))))))]))

(define (compile-atom exps cont)
  (compile-atom-aux exps cont '()))

(define (compile-atom-aux exps cont sofar)
  (if (null? exps)
      (if (= (length sofar) 1)
          `(,cont ,@sofar)
          `(,cont (string-append ,@(reverse sofar))))
      (let [(arg (new-arg))]
        (compile-atom-arg
         (car exps)
         `(lambda (,arg)
           ,(compile-atom-aux (cdr exps) cont (cons arg sofar)))))))

(define (compile-atom-arg exp cont)
  (cond [(string? exp) `(,cont ,exp)]
        [(eq? (car exp) 'var)
         (compile-var (cadr exp) cont)]
        [else
         (let ([arg (new-arg)])
           (if (eq? (car exp) 'bracket)
               (gcomp (cadr exp)
                      `(lambda (,arg) (,cont (.stringify ,arg))))
               (gcomp `(@ ,(cadr exp))
                      `(lambda (,arg) (,cont (flatlist ,arg))))))]))

(define (compile-word-split exp cont)
  (let ([arg (new-arg)])
    (gcomp exp
           `(lambda (,arg)
              (.split-words ,cont ,arg)))))

(define (compile-parencmd cmd cont spliced)
  (if spliced
      (gcomp `(@ ,cmd) cont)
      (gcomp `(@ ,cmd)
             (let ([arg (new-arg)])
               `(lambda (,arg) (,cont (flatlist ,arg)))))))

(define (compile-bracketcmd cmd cont)
  (gcomp cmd cont))

(define (compile-in-field cmd exp cont)
  (let ([arg1 (new-arg)]
        [arg2 (new-arg)])
    (gcomp cmd
           `(lambda (,arg1)
              ,(gcomp exp
                      `(lambda (,arg2)
                         (unless (integer? ,arg2)
                                 (gosh-arg-error "Non-integral field specifier"
                                                 ,arg2))
                         (,cont (.gosh-field-constrain (.gosh-sprint ,arg1)
                                                       ,arg2))))))))

(define (compile-racket-exp exp flag cont)
  (if flag `(,exp ,cont) `(,cont ,exp)))

(define (compile-getpid cont)
  `(,cont (getpid)))

(define (compile-pregexp val cont)
  (let ([arg (new-arg)]
        [vars (gensym "vars-")]
        [pat (gensym "pat-")])
    (gcomp
     val
     `(lambda (,arg)
        (let-values ([(,vars ,pat) (extract-regexp-field-names ,arg)])
          (,cont (gregexp (string-append "$'" ,arg "'") (map strip-$ ,vars)
                          (pregexp ,pat))))))))

(define (compile-fold fun init exp cont)
  (let ([fn (gensym "fun-")]
        [fnresult (gensym "funresult-")]
        [acc (gensym "acc-")]
        [curr (gensym "curr-")])
    (gcomp
     fun
     `(lambda (,fn)
        ,(if init
             (gcomp
              init
              `(lambda (,acc)
                 ,(gcomp
                   exp
                   `(lambda (,curr)
                      (,fn (lambda (,fnresult) (set! ,acc ,fnresult))
                           (mlist ,acc ,curr))))
                 (,cont ,acc)))
             `(let ([,acc #f])
                ,(gcomp
                  exp
                  `(lambda (,curr)
                     (if ,acc
                         (,fn (lambda (,fnresult) (set! ,acc ,fnresult))
                              (mlist ,acc ,curr))
                         (set! ,acc ,curr))))
                (,cont ,acc)))))))

(define (det? exp)
  (match exp
    [(or (? number?) (? symbol?) (? string?) (? char?)) #t]
    [(list 'pregexp val) #t]
    [(list 'atom val) #t]
    [(list 'symbol val) #t]
    [(list 'seq _ arg2) (det? arg2)]
    [(list 'xor _ _) #f]
    [(list 'or _ _) #f]
    [(list 'and arg1 arg2) (and (det? arg1) (det? arg2))]
    [(list 'to arg1 arg2 _) #f]
    [(list '@* arg) #t]
    [(list '@ arg) #t]
    [(list '@* arg chunk) #t]
    [(list '&+ args ...) (andmap det? args)]
    [(list '&++ arg) #f]
    [(list '* arg) #t]
    [(list 'once arg) (det? arg)]
    [(list '! arg) #f]
    [(list '~ arg) #f]
    [(list '~~ arg) #f]
    [(list '- arg) (det? arg)]
    [(list 'elements-of arg) #f]
    [(list-rest 'list args ... pat)
     (andmap det? (if (null? pat) args (cons pat args)))]
    [(list-rest 'tuple args ... pat)
     (andmap det? (if (null? pat) args (cons pat args)))]
    [(list 'hash pairs ...) (andmap (lambda (pair) (andmap det? pair))
                                    pairs)]
    [(list 'set elements ...) (andmap det? elements)]
    [(struct var (_ _)) #t]
    [(list 'fetch table key) #f]
    [(list 'if test t e) (and (det? t) (det? e))]
    [(list ':: args ...) (andmap semidet? args)]
    [(list ':~> var exp) #f]
    [(list ':! name) #t]
    [(list 'function-clause
           (list (and discriminator (or '=! '<! '>! '<? '>? '>~))
                 name pat guard pipe exp)
           start end) #t]
    [(list 'bracefun exp _ _) #f]
    [(list 'pregexp val) (det? val)]
    [(list 'case exp clauses) #f]
    [(list 'set-at exp) #t]
    [(list 'hash-at exp) #t]
    [(list 'str-at exp) #t]
    [(list 'file-input exp) #f]
    [(list 'assoc left right) (and (det? left) (det? right))]
    [(list ':= container arglist item)
     (and (det? container) (det? arglist) (det? item))]
    [(list '-= container item) (and (det? container) (det? item))]
    [(list '+= container item) (and (det? container) (det? item))]
    [(list '++ container item) (and (det? container) (det? item))]
    [(list '// goal solution-number) #f]
    [(list '//* goal) #f]
    [(list 'pipeline item otherpipe err) #f]
    [(list '&&. cmd othercmd) #f]
    [(list '||. cmd othercmd) #f]
    [(list 'assignment var val) #f]
    [(list (list 'redirect source desc mode exp) _) #f]
    [(list 'spliced-parencmd cmd) #t]
    [(list 'parencmd cmd) #t]
    [(list 'bracketcmd cmd) (det? cmd)]
    [(list (list 'in-field cmd exp) _) (and (det? cmd) (det? exp))]
    [(list 'strexps exps) #f]
    [(list 'atomexps exps) #f]
    [(list 'word-split exp) #f]
    [(list 'fold fun init exp) #f]
    [(list 'fold fun exp) #f]
    [(list 'racket exp #t) #f]
    [(list 'racket exp #f) #f]
    [(list 'post
           (list 'post
                 (list 'post exp (list '~> pat))
                 (list (and filt (or 'when 'while) filtexp)))
           (list 'in inexp))
     #f]
    [(list 'post
           (list 'post exp (list '~> pat))
           (list (and filt (or 'when 'while)) filtexp))
     #f]
    [(list 'post exp (list (and filt (or 'when 'while)) filtexp))
     (det? exp)]
    [(list 'post
           (list 'post arg1 (list '~> pat))
           (list 'in arg2))
     #f]
    [(list 'post exp (list '~> pat)) #f]
    [(list 'post arg1 (list 'in arg2)) (and (det? arg1) (det? arg2))]
    [(list 'post arg1 (list '&&> arg2)) (and (det? arg1) (det? arg2))]
    [(list 'post arg1 (list '\|\|> arg2)) #f]
    [(list 'app fun args _) #f]
    [(list 'next args) #f]
    [(list (and op (? simple-binop?)) arg1 arg2)
     (and (det? arg1) (det? arg2) (not (semidet-binop? op)))]))

(define (semidet? exp)
  (match exp
    [(or (? number?) (? symbol?) (? string?) (? char?)) #t]
    [(list 'pregexp val) #t]
    [(list 'atom val) #t]
    [(list 'symbol val) #t]
    [(list 'seq _ arg2) (semidet? arg2)]
    [(list 'xor _ _) #f]
    [(list 'or _ _) #f]
    [(list 'and arg1 arg2) (and (semidet? arg1) (semidet? arg2))]
    [(list 'to arg1 arg2 _) #f]
    [(list '@* arg) #t]
    [(list '@ arg) #t]
    [(list '@* arg chunk) #t]
    [(list '&+ args ...) (andmap semidet? args)]
    [(list '&++ arg) #f]
    [(list '* arg) #t]
    [(list 'once arg) #t]
    [(list '! arg) #t]
    [(list '~ arg) #f]
    [(list '~~ arg) #f]
    [(list '- arg) (semidet? arg)]
    [(list 'elements-of arg) #f]
    [(list-rest 'list args ... pat)
     (andmap semidet? (if (null? pat) args (cons pat args)))]
    [(list-rest 'tuple args ... pat)
     (andmap semidet? (if (null? pat) args (cons pat args)))]
    [(list 'hash pairs ...) (andmap (lambda (pair) (andmap semidet? pair))
                                    pairs)]
    [(list 'set elements ...) (andmap semidet? elements)]
    [(struct var (_ _)) #t]
    [(list 'fetch table key) (and (semidet? table) (semidet? key))]
    [(list 'if test t e) (and (semidet? t) (semidet? e))]
    [(list ':: args ...) (andmap semidet? args)]
    [(list ':~> var exp) (semidet? exp)]
    [(list ':! name) #t]
    [(list 'function-clause
           (list (and discriminator (or '=! '<! '>! '<? '>? '>~))
                 name pat guard pipe exp)
           start end) #t]
    [(list 'pregexp val) (semidet? val)]
    [(list 'bracefun exp _ _) #t]
    [(list 'case exp clauses) #f]
    [(list 'set-at exp) #t]
    [(list 'hash-at exp) #t]
    [(list 'str-at exp) #t]
    [(list 'file-input exp) #f]
    [(list 'assoc left right) (and (semidet? left) (semidet? right))]
    [(list ':= container arglist item)
     (and (semidet? container) (semidet? arglist) (semidet? item))]
    [(list '-= container item) (and (semidet? container) (semidet? item))]
    [(list '+= container item) (and (semidet? container) (semidet? item))]
    [(list '++ container item) (and (semidet? container) (semidet? item))]
    [(list '// goal solution-number) #f]
    [(list '//* goal) #f]
    [(list 'pipeline item otherpipe err) #f]
    [(list '&&. cmd othercmd) #f]
    [(list '||. cmd othercmd) #f]
    [(list 'assignment var val) #t]
    [(list (list 'redirect source desc mode exp) _) #f]
    [(list 'spliced-parencmd cmd) #t]
    [(list 'parencmd cmd) #t]
    [(list 'bracketcmd cmd) (semidet? cmd)]
    [(list (list 'in-field cmd exp) _) (and (semidet? cmd) (semidet? exp))]
    [(list 'strexps exps) #f]
    [(list 'atomexps exps) #f]
    [(list 'word-split exp) #f]
    [(list 'fold fun init exp) #f]
    [(list 'fold fun exp) #f]
    [(list 'racket exp #t) #f]
    [(list 'racket exp #f) #t]
    [(list 'post
           (list 'post
                 (list 'post exp (list '~> pat))
                 (list (and filt (or 'when 'while) filtexp)))
           (list 'in inexp))
     (and (semidet? exp) (semidet? inexp))]
    [(list 'post
           (list 'post exp (list '~> pat))
           (list (and filt (or 'when 'while)) filtexp))
     (semidet? exp)]
    [(list 'post exp (list (and filt (or 'when 'while)) filtexp))
     (semidet? exp)]
    [(list 'post
           (list 'post arg1 (list '~> pat))
           (list 'in arg2))
     (and (semidet? arg1) (semidet? arg2))]
    [(list 'post exp (list '~> pat)) #t]
    [(list 'post arg1 (list 'in arg2)) (and (semidet? arg1) (semidet? arg2))]
    [(list 'post arg1 (list '&&> arg2)) (and (semidet? arg1) (semidet? arg2))]
    [(list 'post arg1 (list '\|\|> arg2)) #f]
    [(list 'app fun args _) #f]
    [(list 'next args) #f]
    [(list (and op (? simple-binop?)) arg1 arg2)
     (or (and (det? arg1) (det? arg2) (semidet-binop? op))
         (and (semidet? arg1) (semidet? arg2)))]))

(define (is-semidet? exp)
  (check-prop exp semidets semidet?))

(define (is-det? exp)
  (check-prop exp dets det?))

(define (check-prop exp prop-hash prop-pred)
  (case (hash-ref (prop-hash) exp 'unknown)
    [(#t) #t]
    [(#f) #f]
    [(unknown)
     (let ([val (prop-pred exp)])
       (hash-set! (prop-hash) exp val)
       val)]))

(define (gcomp exp cont)
  (match exp
    [(or (? symbol?) (? number?) (? string?) (? char?))
     `(,cont ,exp)]
    [(list 'bool val) `(,cont ,val)]
    [(list 'pregexp val) (compile-pregexp val cont)]
    [(list 'atom val) `(,cont ',val)]
    [(list 'symbol val) `(,cont ',val)]
    [(list 'seq arg1 arg2) (compile-seq arg1 arg2 cont)]
    [(list 'xor arg1 arg2) (compile-xor arg1 arg2 cont)]
    [(list 'or arg1 arg2) (compile-or arg1 arg2 cont)]
    [(list 'and arg1 arg2) (compile-and arg1 arg2 cont)]
    [(list 'TO arg1 arg2 step) (compile-to arg1 arg2 step cont)]
    [(list '@* arg) (compile-@* arg cont 1)]
    [(list '@ arg) (compile-@ arg cont)]
    [(list '@* arg chunk) (compile-@* arg cont chunk)]
    [(list '&+ args ...) (compile-&+ args cont)]
    [(list '&++ arg) (compile-&++ arg cont)]
    [(list '* arg) (compile-* arg cont)]
    [(list 'once arg) (compile-once arg cont)]
    [(list '~ arg) (compile-~ arg cont)]
    [(list '~~ arg) (compile-~~ arg cont)]
    [(list '! arg) (compile-! arg cont)]
    [(list '- arg) (compile-- arg cont)]
    [(list 'elements-of arg) (compile-elements-of arg cont)]
    [(list-rest 'list args ... pat) (compile-list (append args pat) cont)]
    [(list-rest 'tuple args ... pat) (compile-tuple (append args pat) cont)]
    [(list 'hash pairs ...) (compile-hash pairs cont)]
    [(list 'set elements ...) (compile-set elements cont)]
    [(struct var (arg _)) (compile-var arg cont)]
    [(list 'fetch table key) (compile-fetch table key cont)]
    [(list 'if test t e) (compile-if test t e cont)]
    [(list ':: args ...) (compile-recseq args cont)]
    [(list ':~> var exp) (compile-recbind var exp cont)]
    [(list ':! func-name) (compile-func-clause-pop func-name cont)]
    [(list 'assoc left right) (compile-assoc left right cont)]
    [(list ':= container arglist item) (compile-:= container arglist item cont)]
    [(list '-= container item) (compile--= container item cont)]
    [(list '+= container item) (compile-+= container item cont)]
    [(list '++ container item) (compile-++ container item cont)]
    [(list '// goal solution-number) (compile-// goal solution-number cont)]
    [(list '//* goal) (compile-//* goal cont)]
    [(list 'pipeline item otherpipe err)
     (compile-pipe item otherpipe err cont)]
    [(list '&&. cmd othercmd)
;;     (printf "spans: ~s~n" (chunks spans))
     (compile-&&. cmd othercmd cont)]
    [(list '||. cmd othercmd)
;;     (printf "spans: ~s~n" (chunks spans))
     (compile-||. cmd othercmd cont)]
    [(list 'assignment var val)
;;     (printf "spans: ~s~n" (chunks spans))
     (compile-assignment var val cont)]
    [(list 'strexps exps) (compile-str exps cont)]
    [(list 'atomexps exps) (compile-atom exps cont)]
    [(list 'word-split exp) (compile-word-split exp cont)]
    [(list 'redirect source desc mode exp)
     (compile-redirect source desc mode exp cont)]
    [(list 'spliced-parencmd cmd) (compile-parencmd cmd cont #t)]
    [(list 'parencmd cmd) (compile-parencmd cmd cont #t)]
    [(list 'bracketcmd cmd) (compile-bracketcmd cmd cont)]
    [(list 'in-field cmd exp)
     (compile-in-field cmd exp cont)]
    [(list 'function-clause
           (list (and discriminator (or '=! '<! '>! '<? '>? '>~))
                 name pat guard pipe exp)
           start end)
     (compile-func-clause discriminator name pat (and guard (cadr guard))
                          pipe exp start end cont)]
    [(list 'function-clause
           (list 'dcgfunc (and discriminator (or '=! '<! '>! '<? '>? '>~))
                 name pat guard exp)
           start end)
     (compile-dcg discriminator name pat (and guard (cadr guard))
                  exp start end cont)]
    [(list 'fun name pat guard pipe exp)
     (compile-anon-func name pat (and guard (cadr guard)) pipe exp cont)]
    [(list 'bracefun exp start end) (compile-bracefun exp start end cont)]
    [(list 'case exp clauses) (compile-case exp clauses cont)]
    [(list 'set-at exp) (compile-set-at exp cont)]
    [(list 'hash-at exp) (compile-hash-at exp cont)]
    [(list 'str-at exp) (compile-str-at exp cont)]
    [(list 'file-input exp) (compile-file-input exp cont)]
    [(list 'post
           (list 'post
                 (list 'post exp (list '~> pat))
                 (list (and filt (or 'when 'while)) filtexp))
           (list 'in inexp))
     (compile-full-post exp pat filt filtexp inexp cont)]
    [(list 'post
           (list 'post exp (list '~> pat))
           (list (and filt (or 'when 'while)) filtexp))
     (compile-match-filter exp pat filt filtexp cont)]
    [(list 'post exp (list (and filt (or 'when 'while)) filtexp))
     (compile-simple-filter exp filt filtexp cont)]
    [(list 'post
           (list 'post arg1 (list '~> pat))
           (list 'in arg2))
     (compile-match-in arg1 pat arg2 cont)]
    ;; [(list 'post
    ;;        (list 'post arg1 (list '~> pat))
    ;;        (list 'in arg2))
    ;;  (compile-match-in arg1 pat arg2 cont)]
    [(list 'fold fun init exp) (compile-fold fun init exp cont)]
    [(list 'fold fun exp) (compile-fold fun #f exp cont)]
    [(list 'racket exp flag) (compile-racket-exp exp flag cont)]
    [(list 'post exp (list '~> pat)) (compile-match exp pat cont)]
    [(list 'post arg1 (list 'in arg2)) (compile-simple-in arg1 arg2 cont)]
    [(list 'post arg1 (list '&&> arg2)) (compile-simple-&&> arg1 arg2 cont)]
    [(list 'post arg1 (list '\|\|> arg2)) (compile-simple-||> arg1 arg2 cont)]
    [(list 'app fun args expand-strs)
;;     (printf "spans: ~s~n" (chunks spans))
     (compile-app fun args expand-strs cont)]
    [(list 'next args) (compile-next args cont)]
    [(list '== arg1 arg2) (compile-unify arg1 arg2 cont)]
    [(list (and op (? simple-binop?)) arg1 arg2)
     (compile-binop op arg1 arg2 cont)]))

(define (simplify item)
  (match item
    [(list (list-rest 'lambda (list arg) body) val)
     #:when (<= (count-tree-eq arg body) 1)
     (simplify (cons 'begin (subst val arg body)))]
    [(list 'begin sub) (simplify sub)]
    [(list 'let '() sub) (simplify sub)]
    [(list-rest 'let (list (list var val)) body)
     #:when (<= (count-tree-eq var body) 1)
     (simplify (cons 'begin (subst val var body)))]
    [(list 'lambda args preexps ... (cons 'begin exps) postexps ...)
     (simplify `(lambda ,args ,@preexps ,@exps ,@postexps))]
    [(list vals ...)
     (let ([simped (map simplify vals)])
       (if (equal? simped vals)
           vals
           (simplify simped)))]
     [_ item]))

(define (count-tree-eq arg tree)
  (if (equal? (.stringify tree) (.stringify arg))
      1
      (match tree
        [(cons kar kdr) (+ (count-tree-eq arg kar) (count-tree-eq arg kdr))]
        [_ 0]))) ; ignoring vectors for right now???

(define (subst val arg tree)
  (if (equal? (.stringify tree) (.stringify arg))
      val
      (match tree
        [(cons kar kdr) (cons (subst val arg kar) (subst val arg kdr))]
        [_ tree]))) ; ignoring vectors for right now???

(define (trans expstr)
  (simplify (gosh-compile (gosh expstr 'colon) '(lambda (x) x))))

(define (strans expstr)
  (simplify (gosh-compile (gosh expstr 'default) '(lambda (x) x))))

(define (gosh-compile exp cont)
  (set! exp (depos exp))
;  (when (getenv "GOSH_PPRINT") (pprint #t))
;  (when (getenv "GOSH_PPRINT_PARSED") (pretty-print exp))
  (parameterize [(dets (make-hasheq))
                 (semidets (make-hasheq))
                 (app-refs '())
                 (clause-names '())
                 (top-level-vars (mutable-set))]
    (let ([compiled (gcomp exp cont)])
      ;; (when (pprint)
      ;;   (pretty-print (simplify compiled)))
      `(begin
         ,@(map (lambda (v) `(define ,v #f)) (set->list (top-level-vars)))
         (for-each .set-up-external-prog-lookup! ',(app-refs))
         ,compiled))))

;; Assumes caller has set up 'app-refs' list parameter and wants to
;; gather across calls to gosh-file-compile

(define (gosh-file-compile exp cont)
  (set! exp (depos exp))
  (when (getenv "GOSH_PPRINT") (pprint #t))
  (when (getenv "GOSH_PPRINT_PARSED") (pretty-print exp))
  (parameterize [(dets (make-hasheq))
                 (semidets (make-hasheq))]
    (let ([compiled (gcomp exp cont)])
      (when (pprint)
        (pretty-print (simplify compiled)))
      compiled)))

;;(trace gosh-compile compile-simple-filter compile-full-post compile-match-filter compile-match-in compile-simple-match compile-dcg compile-func-clause to-pat)

#lang racket/base
(require parser-tools/yacc
         parser-tools/lex
         "lex.rkt"
         racket/async-channel
         racket/trace
         racket/match
         racket/format
         racket/pretty
         (prefix-in : parser-tools/lex-sre))

(provide (all-defined-out))
;; (provide parse rparse rlex gosh token-EOF var var-name var?
;;          extract-regexp-field-names)

(define (ppwrap . things-to-pprint)
  (for ([item (in-list things-to-pprint)])
       (pretty-print item (current-error-port)))
  (let loop ([l things-to-pprint])
    (if (null? (cdr l))
        (car l)
        (loop (cdr l)))))

(struct var (name [seen #:mutable]) #:transparent)
(struct pos (val pos) #:transparent)

(define (depos x)
  (match x
         [(struct pos (val _)) val]
         [_ x]))

(define current-exp-string (make-parameter ""))

;; (define-lex-abbrevs
;;  (lower-letter (:/ "a" "z"))
;;  (upper-letter (:/ #\A #\Z))
;;  (digit (:/ "0" "9"))
;;  (integer (:+ digit))
;;  (fraction (:: integer (:? (:: "/" integer))))
;;  (real (:: integer (:? (:: #\. integer))))
;;  (complex (:: (:or real fraction) (:or "+" "-") (:? (:or real fraction)) "i"))
;;  (sym (:or "+" "-" "*" "/" "^" "@" "&" "$" "_" "**" "&&" "!" "!=" "~" ":" ":~"
;;            "=" "<-" "-=" "+=" "=!" "=>" "->" "<!" ":>" ":<?" ":>?" ":!"
;;            "==" ">" ">=" "<" "<=" "::")))

;; (define lex
;;   (lexer
;;    [(eof) 'EOF]
;;    [(:: "#" (:* (:~ #\newline))) (lex input-port)]
;;    [(:or #\tab #\space) (lex input-port)]
;;    [#\newline (token-newline)]
;;    [sym (string->symbol lexeme)]
;;    [(:: "$" digit) (token-VAR (string->symbol lexeme))]
;;    [(:: "$" (:+ lower-letter) (:* (:or lower-letter upper-letter digit "_" )))
;;     (token-VAR (string->symbol lexeme))]
;;    [(:: "${" (:+ lower-letter)
;;         (:* (:or lower-letter upper-letter digit "_" )) "}")
;;     (token-VAR (string->symbol
;;                 (string-append "$"
;;                                (substring
;;                                 lexeme 2 (sub1 (string-length lexeme))))))]
;;    [".." 'DOTDOT]
;;    ["." 'DOT]
;;    ["||" 'OR]
;;    [";" 'SEMI]
;;    ["(" 'LPAR]
;;    [")" 'RPAR]
;;    ["{" 'LBRACE]
;;    ["}" 'RBRACE]
;;    ["[" 'LBRACK]
;;    ["]" 'RBRACK]
;;    ["&[" 'HBRACK]
;;    ["," 'COMMA]
;;    ["if" 'IF]
;;    ["elif" 'ELIF]
;;    ["else" 'ELSE]
;;    ["then" 'THEN]
;;    ["fi" 'FI]
;;    ["in" 'IN]
;;    ["when" 'WHEN]
;;    ["while" 'WHILE]
;;    ["next" 'NEXT]
;;    ["rem" 'REM]
;;    ["end" 'END]
;;    ["%?" 'COUNT]
;;    ["|>" 'PIPEIN]
;;    ["|" 'PIPE]
;;    [(:: (:+ "%") (:+ digit)) (token-SEQVAR (string->symbol lexeme))]
;;    [(:+ "%") (token-ANON (string->symbol lexeme))]
;;    [(:: "$\"" (:* (:or "\\\"" (:~ "\""))) "\"")
;;     (token-REGEX (string-trim (substring lexeme 1) "\""))]
;;    [(:: "\"" (:* (:or "\\\"" (:~ "\""))) "\"")
;;     (token-STR (string-trim lexeme "\""))]
;;    [(:: real "/" real)
;;     (token-NUM (apply / (map string->number (string-split lexeme "/"))))]
;;    [(:or fraction real complex) (token-NUM (string->number lexeme))]
;;    [(:: "'" (:* (:~ "'")) "'")
;;     (token-ATOM (string->symbol (string-trim lexeme "'")))]
;;    [(:: (:* (:or lower-letter upper-letter digit "_" "/" "-"))
;;         (:or lower-letter upper-letter)
;;         (:* (:or lower-letter upper-letter digit "_" "/" "-")))
;;     (token-ATOM (string->symbol lexeme))]))

(define (print-error str pos)
  (define (eol-offset s)
    (define str-len (string-length s))
    (let loop [(index 0)]
      (cond [(>= index str-len) str-len]
            [(eqv? (string-ref s index) #\newline) index]
            [else (loop (add1 index))])))
  (define (header-lines s i)
    (if (<= i 0)
        'done
        (let ([eol (eol-offset s)])
          (printf "~a~%" (substring s 0 eol))
          (when (> (string-length s) eol)
                (header-lines (substring s (add1 eol)) (sub1 i))))))
  (define lines (position-line pos))
  (define column (position-col pos))

  (header-lines str lines)
  (printf "~a^ here~%" (make-string (if (> lines 1)
                                        (- column 2)
                                        (sub1 column))
                                    #\space)))

(define parse
  (parser
   (start start)
   (end EOF)
   (tokens value-tokens sym-tokens)
   (error (lambda (a tok c start end)
            (print-error (current-exp-string) start)
            (error (format "Unexpected token: '~a'"
                           (or (hash-ref printtab tok #f)
                               tok)))))
   (precs (nonassoc =! -> <! >! :! <? >? >~)
          (left SEMI)
          (right ||. PIPEPIPE)
          (right &&. AMPAMP)
          (right PIPE PIPEAMP)
          (nonassoc =>)
          (left XOR)
          (left OR)
          (left &&)
          (nonassoc :~>)
          (nonassoc //)
          (nonassoc //*)
          (nonassoc &/)
          (right IN &&> \|\|>)
          (left WHEN WHILE)
          (nonassoc ~>)
          (right ::)
          (nonassoc ! ~ ~~)
          (nonassoc !=)
          (left == > >= < <=)
          (left <-)
          (nonassoc &+)
          (nonassoc TO)
          (nonassoc BY FROM)
          (left -= += ++)
          (left - +)
          (left * / REM)
          (nonassoc @:)
          (left BQUOTE @ @* SETAT HASHAT STRAT & ^)
          (right **)
          (left NEG)
          (nonassoc <.)
          (nonassoc APP NEXT)
          (nonassoc LBRACK HBRACK SBRACE))
   (debug "/tmp/parser")
   (src-pos)
   (grammar
    (start [() #f]
           ;; If there is an error, ignore everything before the error
           ;; and try to start over right after the error
           [(error start) $2]
           [(toplevel) $1])
    (toplevel
     [(: function-clause DOT) `(function-clause ,$2 ,$1-start-pos ,$3-end-pos)]
     [(function-clause-pop) $1]
     [(: IMPORT mod-ref import-tail DOT) `(import ,$3 ,$4)]
     [(: exp DOT) $2]
     [(cmd) $1])
    (mod-ref
     [(ATOM) $1]
     [(< ATOM >) `(library ,$2)])
    (import-tail
     [(EXCEPT specific-imports) `(except ,$2)]
     [(ONLY specific-imports) `(only ,$2)]
     [() 'all])
    (specific-imports
     [(LBRACK si si-tail) (cons $2 $3)])
    (si-tail
     [(COMMA si si-tail) (cons $2 $3)]
     [(RBRACK) '()])
    (si
     [(ATOM) $1]
     [(ATOM => ATOM) `(,$1 ,$3)])
    (cmd
     [(simple-cmd AMPAMP cmd)
      (pos
       `(&&. ,(pos-val $1) ,(pos-val $3))
       (append (pos-pos $1)
               (cons (list $2-start-pos $2-end-pos)
                     (pos-pos $3))))]
     [(simple-cmd PIPEPIPE cmd)
      (pos `(||. ,(pos-val $1) ,(pos-val $3))
           (append (pos-pos $1)
                   (cons (list $2-start-pos $2-end-pos)
                         (pos-pos $3))))]
     [(simple-cmd) $1])
    (simple-cmd
     [(cmd-item cmd-items cmd-tail)
      (pos (process-cmd-chain (pos-val $1) (pos-val $2) (pos-val $3))
           (append (pos-pos $1) (pos-pos $2) (pos-pos $3)))])
    (cmd-item
     [(ATOM) (pos (process-tilde $1) (list (list $1-start-pos $1-end-pos)))]
     [(FUNKYATOM) (pos `(atom ,$1) `((,$1-start-pos ,$1-end-pos)))]
     [(VAR) (pos $1 (list (list $1-start-pos $1-end-pos)))]
     [(atomstr) (pos $1 (list (list $1-start-pos (position (sub1 (position-offset $1-end-pos)) 1 (sub1 (position-offset $1-end-pos))))))]
     [(cstr) (pos $1 (list (list $1-start-pos $1-end-pos)))]
;;;     [(LBRACE cmd RBRACE) `(bracecmd ,$2)]
     [(DOLLAR COLONLPAR exp RPAR)
      (pos `(parencmd ,$3) `((,$1-start-pos ,$4-end-pos)))]
     [(DOLLAR COLONLBRACK exp RBRACK)
      (pos $3 (list (list $1-start-pos $4-end-pos)))]
     [(DOLLAR COLONLBRACK exp COMMA exp RBRACK)
      (pos `(in-field ,$3 ,$5)
           `((,$1-start-pos ,$5-end-pos)))]
     [(DOLLAR DOTLPAR cmd RPAR) (pos `(parencmd ,(pos-val $3))
                                     `((,$1-start-pos ,$4-end-pos)))]
     [(DOLLAR DOTLBRACK cmd RBRACK)
      (pos $3 (list (list $1-start-pos $4-end-pos)))]
     [(DOLLAR DOTLBRACK cmd COMMA exp RBRACK)
      (pos `(in-field ,$3 ,$5)
           `((,$1-start-pos ,$5-end-pos)))]
     [(DOLLAR LPAR cmd RPAR)
      (begin (printf "EP1: ~s~n" $4-end-pos)
      (pos `(parencmd ,(depos $3)) `((,$1-start-pos ,$4-end-pos))))]
     [(DOLLAR LBRACK cmd RBRACK)
      (pos $3 (list (list $1-start-pos $4-end-pos)))]
     [(DOLLAR LBRACK cmd COMMA exp RBRACK)
      (pos `(in-field ,(depos $3) ,$5)
           `((,$1-start-pos ,$5-end-pos)))])
    (cmd-items
     [(cmd-item cmd-items) (pos (cons (pos-val $1) (pos-val $2))
                                (append (pos-pos $1) (pos-pos $2)))]
     [() (pos '() '())])
    (cmd-tail
     [(LT cmd-item cmd-tail) (pos `(pipe-input ,(pos-val $2) ,(pos-val $3))
                                  (list* (list $1-start-pos $1-end-pos)
                                         (append (pos-pos $2) (pos-pos $3))))]
     [(PIPE simple-cmd) (pos `(pipe ,(pos-val $2))
                             (cons (list $1-start-pos $1-end-pos)
                                   (pos-pos $2)))]
     [(PIPEAMP simple-cmd)
      (pos `(pipeamp ,(pos-val $2))
           (cons (list $1-start-pos $1-end-pos) (pos-pos $2)))]
     [(GT cmd-item) (pos `(redirect 1 truncate/replace ,(pos-val $2))
                         (cons (list $1-start-pos $1-end-pos) (pos-pos $2)))]
     [(GTGT cmd-item) (pos `(redirect 1 append ,(pos-val $2))
                           (cons (list $1-start-pos $1-end-pos) (pos-pos $2)))]
     [(GTAMP cmd-item) (pos `(redirect both truncate/replace ,(pos-val $2))
                            (cons (list $1-start-pos $1-end-pos) (pos-pos $2)))]
     [(SEMI) (pos '() '())]
     ;; [(AMPAMP cmd) `(&&. ,$2)]
     ;; [(PIPEPIPE cmd) `(||. ,$2)]
     [() (pos '() '())])
    (function-clause
     [(=! ATOM arg-pat guard pipe exp)
      `(=! ,$2 ,$3 ,$4 ,$5, $6)]
     [(<! ATOM arg-pat guard pipe exp)
      `(<! ,$2 ,$3 ,$4 ,$5, $6)]
     [(>! ATOM arg-pat guard pipe exp)
      `(>! ,$2 ,$3 ,$4 ,$5, $6)]
     [(<? ATOM arg-pat guard pipe exp)
      `(<? ,$2 ,$3 ,$4 ,$5, $6)]
     [(>? ATOM arg-pat guard pipe exp)
      `(>? ,$2 ,$3 ,$4 ,$5, $6)]
     [(>~ ATOM arg-pat guard pipe exp)
      `(>~ ,$2 ,$3 ,$4 ,$5, $6)])
    (guard [(WHEN exp) `(when (once ,$2))]
           [() #f])
    (pipe [(PIPEIN pat ->) $2]
          [(PIPEIN ->) #t]
          [(UPPIPEIN pat ->) `(up ,$2)]
          [(UPPIPEIN ->) `(up #t)]
          [(->) #f])
    (function-clause-pop
     [(:! ATOM DOT) `(:! ,$2)])
    (exp [(NUM) $1]
         [(ATOM) `(atom ,$1)]
         [(SYMBOL) `(symbol ,$1)]
         [(CHAR) $1]
         [(ANON) $1]
         [(SEQVAR) $1]
         [(COUNT) '%?]
         [(VAR) (var $1 #f)]
         [(TRUE) '(bool #t)]
         [(FALSE) '(bool #f)]
         [(RACKET) `(racket ,(read (open-input-string $1)) #t)]
         [(SIMPLERACKET) `(racket ,(read (open-input-string $1)) #f)]
;         [(exp SEMI exp) `(seq (once ,$1) ,$3)]
         [(exp PIPE exp) `(pipeline ,$1 ,$3 #f)]
         [(exp PIPEAMP exp) `(pipeline ,$1 ,$3 #t)]
         [(exp &&. exp) `(&&. ,$1 ,$3)]
         [(exp ||. exp) `(||. ,$1 ,$3)]
         [(exp XOR exp) `(xor ,$1 ,$3)]
         [(exp OR exp) `(or ,$1 ,$3)]
         [(exp && exp) `(and ,$1 ,$3)]
         [(exp != exp) `(!= ,$1 ,$3)]
         [(exp == exp) `(== ,$1 ,$3)]
         [(exp > exp) `(> ,$1 ,$3)]
         [(exp >= exp) `(>= ,$1 ,$3)]
         [(exp < exp) `(< ,$1 ,$3)]
         [(exp <= exp) `(<= ,$1 ,$3)]
         [(exp + exp) `(+ ,$1 ,$3)]
         [(exp - exp) `(- ,$1 ,$3)]
         [(exp * exp) `(* ,$1 ,$3)]
         [(exp / exp) `(/ ,$1 ,$3)]
         [(exp -= exp) `(-= ,$1 ,$3)]
         [(exp += exp) `(+= ,$1 ,$3)]
         [(exp ++ exp) `(++ ,$1 ,$3)]
         [(exp // exp) `(once (// ,$1 ,$3))]
         [(exp //*) `(once (//* ,$1))]
         [(exp :: exp) `(:: ,$1 ,@(cflatten $3))]
         [(DOLLAR DOTLPAR cmd RPAR) `(parencmd ,(depos $3))]
         [(DOLLAR COLONLPAR exp RPAR) `(parencmd ,$3)]
         [(DOLLAR LPAR exp RPAR) `(parencmd ,$3)]
         [(DOLLAR DOTLBRACK cmd RBRACK) (depos $3)]
         [(DOLLAR DOTLBRACK cmd COMMA exp RBRACK)
          (pos `(in-field ,(depos $3) ,$5) '())]
         [(DOLLAR COLONLBRACK exp RBRACK) $3]
         [(DOLLAR COLONLBRACK exp COMMA exp RBRACK)
          (pos `(in-field ,$3 ,$5) '())]
         [(DOLLAR LBRACK exp RBRACK) $3]
         [(DOLLAR LBRACK exp COMMA exp RBRACK) (pos `(in-field ,$3 ,$5) '())]
         [(exp REM exp) `(remainder ,$1 ,$3)]
         [(exp ** exp) `(** ,$1 ,$3)]
         [(to-exp) $1]
         [(:~> VAR <- exp) `(:~> ,$2 ,$4)]
         [(! exp) `(! ,$2)]
         [(~ exp) `(~ ,$2)]
         [(~~ exp) `(~~ ,$2)]
         [(- exp) (prec NEG) `(- ,$2)]
         [(* exp) (prec NEG) `(* ,$2)]
         [(BQUOTE exp) `(once ,$2)]
         [(@ exp) `(@ ,$2)]
         [(@* exp) `(@* ,$2)]
         [(@: LPAR exp COMMA exp RPAR) `(@* ,$5 ,$3)]
         [(&+ LPAR exp SEMI &+tail) `(&+ ,$3 ,@$5)]
         [(&+ exp) `(&++ ,$2)]
         [(SETAT exp) (list 'set-at $2)]
         [(HASHAT exp) (list 'hash-at $2)]
         [(HASHANON) '|&[%]|]
         [(fun &/ LPAR exp SEMI exp RPAR) `(fold ,$1 ,$4 ,$6)]
         [(fun &/ exp) `(fold ,$1 ,$3)]
         [(STRAT exp) (list 'str-at $2)]
;         [(& exp) `(& ,$2)]
         [(^ exp) `(elements-of ,$2)]
         [(<. exp) `(file-input ,$2)]
         [(list) $1]
         [(tuple) $1]
         [(set) $1]
         [(hash) $1]
         [(hash-type) $1]
         [(DOLLAR str) `(pregexp ,$2)]
         [(DOLLAR ATOM) `(pregexp ,$2)]
         [(assoc) $1]
         [(str) $1]
         [(exp post) `(post ,$1 ,$2)]
         [(fun arglist <- exp) `(:= ,$1 ,$2 ,$4)]
         [(fun arglist) (prec APP) `(app ,$1 ,$2 #f)]
         [(NEXT arglist) `(next ,$2)]
         [(FUN ATOM arg-pat guard pipe exp END) `(fun ,$2 ,$3 ,$4 ,$5 ,$6)]
         [(FUN arg-pat guard pipe exp END) `(fun #f ,$2 ,$3 ,$4 ,$5)]
         [(IF exp THEN exp iftail) `(if (once ,$2) ,$4 ,$5)]
         [(CASE exp OF case-clauses END) `(case ,$2 ,$4)]
         [(LOOP ATOM WITH var-bindings -> exp END)
          `(app (fun ,$2 ,(bindings->argpat $4) #f -> ,$6)
                 ,(binding-values $4) #f)]
         [(LBRACE exp RBRACE) `(bracefun ,$2 ,$1-start-pos ,$3-end-pos)]
         [(LBRACE standard-binop RBRACE)
          `(bracefun ,$2 ,$1-start-pos ,$3-end-pos)]
         [(LBRACE ~> pat RBRACE) `(bracefun (~> ,$3) ,$1-start-pos ,$4-end-pos)]
         [(LPAR exp RPAR) $2])
    ;;      [(LPAR keyword RPAR) $2])
    ;; (keyword [(IF) '(atom if)]
    ;;          [(ELIF) '(atom elif)]
    ;;          [(ELSE) '(atom else)]
    ;;          [(THEN) '(atom then)]
    ;;          [(FI) '(atom fi)]
    ;;          [(IN) '(atom in)]
    ;;          [(FUN) '(atom fun)]
    ;;          [(WHEN) '(atom when)]
    ;;          [(WHILE) '(atom while)]
    ;;          [(NEXT) '(atom next)]
    ;;          [(REM) '(atom rem)]
    ;;          [(END) '(atom end)]
    ;;          [(CASE) '(atom case)]
    ;;          [(OF) '(atom of)]
    ;;          [(TO) '(atom to)]
    ;;          [(BY) '(atom by)]
    ;;          [(LOOP) '(atom loop)]
    ;;          [(WITH) '(atom with)])
    (&+tail [(exp RPAR) (list $1)]
            [(exp SEMI &+tail) (cons $1 $3)])
    (to-exp [(exp TO exp) `(TO ,$1 ,$3 1)]
            [(exp TO exp BY exp) `(TO ,$1 ,$3 ,$5)]
            [(FROM exp BY exp) `(TO ,$2 * ,$4)])
    (var-bindings [(var-binding var-binding-tail) (cons $1 $2)])
    (var-binding [(pat <~ exp) (list $1 $3)])
    (var-binding-tail [() '()]
                      [(COMMA var-binding var-binding-tail)
                       (cons $2 $3)])
    (case-clause [(=! arg-pat guard -> exp)
                  `(=! ,$2 ,$3 ,$5)]
                 [(<! arg-pat guard -> exp)
                  `(<! ,$2 ,$3 ,$5)]
                 [(>! arg-pat guard -> exp)
                  `(>! ,$2 ,$3 ,$5)]
                 [(<? arg-pat guard -> exp)
                  `(<? ,$2 ,$3 ,$5)]
                 [(>? arg-pat guard -> exp)
                  `(>? ,$2 ,$3 ,$5)]
                 [(>~ arg-pat guard -> exp)
                  `(>~ ,$2 ,$3 ,$5)])
    (case-clauses [(case-clause case-clause-tail) (cons $1 $2)])
    (case-clause-tail [(case-clause case-clause-tail) (cons $1 $2)]
                      [() '()])
    (standard-binop [(+) '+]
                    [(-) '-]
                    [(*) '*]
                    [(/) '/]
                    [(**) '**]
                    [(!=) '!=]
                    [(==) '==]
                    [(>) '>]
                    [(>=) '>=]
                    [(<) '<]
                    [(<=) '<=]
                    [(+=) '+=]
                    [(++) '++]
                    [(REM) 'remainder])
    (atomstr [(ATOMBOUND atomstrtail)
              (match $2
                     [(list (list 'paren exp))
                      `(parencmd (word-split ,exp))]
                     [(list (list 'bracket exp))
                      `(bracketcmd (word-split ,exp))]
                     [_ `(word-split
                          (atomexps
                           ,(map process-tilde $2)))])])
    (atomstrtailexp [(STR) $1]
                    [(VAR) `(var ,$1)]
                    [(DOLLAR COLONLPAR exp RPAR) `(paren ,$3)]
                    [(DOLLAR COLONLBRACK exp RBRACK)
                     `(bracket ,$3)]
                    [(DOLLAR DOTLPAR cmd RPAR) `(paren ,(depos $3))]
                    [(DOLLAR DOTLBRACK cmd RBRACK) `(bracket ,$3)]
                    [(DOLLAR LPAR cmd RPAR) `(paren ,(depos $3))]
                    [(DOLLAR LBRACK cmd RBRACK) `(bracket ,(depos $3))])
    (atomstrtail [(atomstrtailexp atomstrtail) (cons $1 $2)]
                 [(STRBOUND) '()])
    (str [(STRBOUND strtail) `(strexps ,$2)])
    (strtailexp [(STR) $1]
                [(VAR) `(var ,$1)]
                [(DOLLAR COLONLPAR exp RPAR) `(paren ,$3)]
                [(DOLLAR COLONLBRACK exp RBRACK) `(bracket ,$3)]
                [(DOLLAR DOTLPAR cmd RPAR) `(paren ,(depos $3))]
                [(DOLLAR DOTLBRACK cmd RBRACK) `(bracket ,(depos $3))]
                [(DOLLAR LPAR exp RPAR) `(paren ,$3)]
                [(DOLLAR LBRACK exp RBRACK) `(bracket ,$3)])
    (strtail [(strtailexp strtail) (cons $1 $2)]
             [(STRBOUND) '()])
    (cstr [(STRBOUND cstrtail) `(strexps ,$2)])
    (cstrtailexp [(STR) $1]
                 [(VAR) `(var ,$1)]
                 [(DOLLAR COLONLPAR exp RPAR) `(paren ,$3)]
                 [(DOLLAR COLONLBRACK exp RBRACK) `(bracket ,$3)]
                 [(DOLLAR DOTLPAR cmd RPAR) `(paren ,(depos $3))]
                 [(DOLLAR DOTLBRACK cmd RBRACK) `(bracket ,(depos $3))]
                 [(DOLLAR LPAR cmd RPAR) `(paren ,(depos $3))]
                 [(DOLLAR LBRACK cmd RBRACK) `(bracket ,(depos $3))])
    (cstrtail [(cstrtailexp cstrtail) (cons $1 $2)]
              [(STRBOUND) '()])
    (datastruct [(str) $1]
                [(VAR) (var $1 #f)]
                [(ANON) $1]
                [(SEQVAR) $1]
                [(set) $1]
                [(hash) $1]
                [(list) $1]
                [(tuple) $1])
    (fun [(ATOM) `(atom, $1)]
         [(datastruct) $1]
         [(DOLLAR str) `(pregexp ,$2)]
         [(DOLLAR ATOM) `(pregexp ,$2)]
         [(LBRACE exp RBRACE) `(bracefun ,$2 ,$1-start-pos ,$3-end-pos)]
         [(LBRACE standard-binop RBRACE)
          `(bracefun ,$2 ,$1-start-pos ,$3-end-pos)]
         [(LBRACE ~> pat RBRACE) `(bracefun (~> ,$3) ,$1-start-pos ,$4-end-pos)]
         [(LPAR exp RPAR) $2])
    (assoc [(exp => exp) `(assoc ,$1 ,$3)])
    (pat [(lvarpat) `(or ,(car $1) (lvar (? (.assign-var ',(cadr $1)))))]
		 [(constraintpat) `(or (lvar (? .constrain-var)) ,$1)]
		 [(nonlvarpat) $1])
	(nonlvarpat [(VAR) $1]
				[(_) '_]
				[(LPAR nonlvarpat RPAR) $2]
				[(VAR = LPAR nonlvarpat RPAR) `(and ,$4 ,$1)])
	(constraintpat [(DOLLAR STRBOUND STR STRBOUND)
					(let-values ([(vars pat) (extract-regexp-field-names $3)])
					  `(pregexp ,pat (list _ ,@vars)))]
				   [(DOLLAR ATOM)
					(let-values ([(vars pat) (extract-regexp-field-names $2)])
					  `(pregexp ,pat (list _ ,@vars)))]
				   [(STRBOUND STR STRBOUND)
					(translate-globs $2)])
	(lvarpat [(NUM) $1]
			 [(STRBOUND STRBOUND) ""]
			 [(ATOM) $1]
			 [(SYMBOL) $1]
			 [(assoc-pat) $1]
			 [(list-pat) $1]
			 [(tuple-pat) $1]
			 [(hash-pat) $1]
			 [(set-pat) $1]
			 [(LPAR lvarpat RPAR) $2]
			 [(VAR = LPAR lvarpat RPAR) `(and ,$4 ,$1)])
    ;; (pat [(VAR) $1]
    ;;      [(VAR = LPAR pat RPAR) `(and ,$4 ,$1)]
    ;;      [(NUM) $1]
    ;;      [(STRBOUND STRBOUND) ""]
    ;;      [(STRBOUND STR STRBOUND)
    ;;       (translate-globs $2)]
    ;;      [(ATOM) $1]
    ;;      [(SYMBOL) $1]
    ;;      [(DOLLAR STRBOUND STR STRBOUND)
    ;;       (let-values ([(vars pat) (extract-regexp-field-names $3)])
    ;;         `(pregexp ,pat (list _ ,@vars)))]
    ;;      [(DOLLAR ATOM)
    ;;       (let-values ([(vars pat) (extract-regexp-field-names $2)])
    ;;         `(pregexp ,pat (list _ ,@vars)))]
    ;;      [(_) '_]
    ;;      [(assoc-pat) $1]
    ;;      [(list-pat) $1]
    ;;      [(tuple-pat) $1]
    ;;      [(hash-pat) $1]
    ;;      [(set-pat) $1]
    ;;      [(LPAR pat RPAR) $2])
    (assoc-pat [(pat => pat) `(association ,$1 ,$3)])
    (post [(~> pat) `(~>, $2)]
          [(filter) $1]
          [(&&> exp) `(&&> ,$2)]
          [(\|\|> exp) `(\|\|> ,$2)]
          [(IN exp) `(in ,$2)])
    (filter [(WHEN exp) `(when (once ,$2))]
            [(WHILE exp) `(while (once ,$2))])
    (iftail [(ELIF exp THEN exp iftail) `(if (once ,$2) ,$4 ,$5)]
            [(ELSE exp FI) $2]
            [(FI) #f])
    (arglist [(list) $1]
             [(tuple) $1]
             [(VAR) $1]
             [(LPAR exp RPAR) $2])
    (set [(SBRACE set-val) (cons 'set $2)])
    (set-val [(RBRACE) '()]
             [(exp set-tail) (cons $1 $2)])
    (set-tail [(RBRACE) '()]
              [(COMMA exp set-tail) (cons $2 $3)])
    (set-pat [(SBRACE set-pat-val)
              (cond [(null? $2) '(? .set-empty?)]
                    [(eq? $2 'dotdotdot) '(? set?)]
                    [else `(? ,(member-test-fun $2))])])
    (set-pat-val [(RBRACE) '()]
                 [(DOTDOTDOT RBRACE) 'dotdotdot]
                 [(self-eval-pat set-pat-tail)
                  (cons $1 $2)])
    (set-pat-tail [(RBRACE) '()]
                  [(COMMA DOTDOTDOT RBRACE) '(dotdotdot)]
                  [(COMMA self-eval-pat set-pat-tail)
                   (cons $2 $3)])
    (self-eval-pat [(NUM) $1]
                   [(ATOM) $1]
                   [(SYMBOL) `',$1]
                   [(CHAR) $1]
                   [(TRUE) #t]
                   [(FALSE) #f])
    (hash [(HBRACK hash-val) (cons 'hash $2)])
    (hash-val [(RBRACK) '()]
              [(assoc hash-tail) (cons $1 $2)])
    (hash-tail [(RBRACK) '()]
               [(COMMA assoc hash-tail) (cons $2 $3)])
    (hash-type [(& < ATOM > LBRACK hash-val) `(hash-type ,$3 ,@$6)])
    (hash-pat [(HBRACK hash-pat-val)
               (cond [(null? $2) '(? .hash-empty?)]
                     [(eq? $2 'dotdotdot) '(? hash?)]
                     [else `(hash-table ,@$2)])])
    (hash-pat-val [(RBRACK) '()]
                  [(DOTDOTDOT RBRACK) 'dotdotdot]
                  [(hash-assoc-pat hash-pat-tail)
                   (cons `(,(car $1) ,(cadr $1)) $2)])
    (hash-pat-tail [(RBRACK) '()]
                   [(COMMA DOTDOTDOT RBRACK) '(_ ...)]
                   [(COMMA hash-assoc-pat hash-pat-tail)
                    (cons `(,(car $2) ,(cadr $2)) $3)])
    (hash-assoc-pat [(self-eval-pat => pat) (list $1 $3)])
    (tuple [(LPAR RPAR) (list 'tuple)]
           [(LPAR exp COMMA RPAR) (list 'tuple $2)]
           [(LPAR exp tuple-tail) (list* 'tuple $2 $3)])
    (tuple-tail [(COMMA exp RPAR) (list $2)]
                [(COMMA exp tuple-tail) (cons $2 $3)])
    (tuple-pat [(LPAR RPAR) '(vector)]
               [(LPAR DOTDOTDOT RPAR) '(? vector?)]
               [(LPAR pat COMMA RPAR) `(vector $2)]
               [(LPAR pat tuple-pat-tail) `(vector ,@(cons $2 $3))])
    (tuple-pat-tail [(COMMA pat RPAR) (list $2)]
                    [(COMMA DOTDOTDOT RPAR) '(_ ...)]
                    [(COMMA pat tuple-pat-tail) (cons $2 $3)])
    (list [(LBRACK list-val) (cons 'list $2)])
    (list-val [(RBRACK) '()]
              [(exp list-tail) (cons $1 $2)])
    (list-tail [(RBRACK) '()]
               [(DOT exp RBRACK) (box $2)]
               [(COMMA exp list-tail) (cons $2 $3)])
    (list-pat [(LBRACK list-pat-val) $2])
    (list-pat-val [(RBRACK) ''()]
                  [(DOTDOTDOT RBRACK) '(or '() (cons _ _) (mcons _ _))]
                  [(pat list-pat-tail) `(or (cons ,$1 ,$2)
                                            (? .force (mcons ,$1 ,$2)))])
    (list-pat-tail [(RBRACK) ''()]
                   [(DOT pat RBRACK) $2]
                   [(COMMA DOTDOTDOT RBRACK) '_]
                   [(COMMA pat list-pat-tail)
                    `(or (cons ,$2 ,$3) (? .force (mcons ,$2 ,$3)))])
    (arg-pat [(VAR) $1]
             [(VAR = LPAR pat RPAR) `(and ,$4 ,$1)]
             [(LPAR pat RPAR) $2]
             [(tuple-pat) $1]
             [(list-pat) $1]))))

(define (member-test-fun elements)
  (let* ([no-dots (remove 'dotdotdot elements)]
         [includes-dots? (not (= (length elements) (length no-dots)))]
         [set-var-in (gensym "set-in")]
         [set-var (gensym "set-")]
         [tests (map (lambda (element)
                       `(set-member? ,set-var ,element))
                     no-dots)]
         [all-tests (if includes-dots?
                        tests
                        (cons `(= (set-count ,set-var) ,(length no-dots))
                              tests))])
    `(lambda (,set-var-in) (define ,set-var (deref ,set-var-in)) (and (set? ,set-var) ,@all-tests))))

(define (process-tilde exp)
  (match exp
         [(and (? string?) arg)
          (path->string (expand-user-path arg))]
         [_ exp]))

(define (process-cmd-chain fun args tail)
  (define (process-tail app-exp tail-exp)
    (cond [(null? tail-exp) app-exp]
          [(eq? (car tail-exp) 'redirect)
           `(redirect ,app-exp ,@(cdr tail-exp))]
          [(eq? (car tail-exp) 'pipe)
           `(pipeline ,app-exp ,(cadr tail-exp) #f)]
          [(eq? (car tail-exp) 'pipeamp)
           `(pipeline ,app-exp ,(cadr tail-exp) #t)]
          [(eq? (car tail-exp) 'pipe-input)
           (let* ([input-pipe `(file-input ,(cadr tail-exp))]
                  [piped-app `(pipeline ,input-pipe ,app-exp #f)])
             (if (null? (caddr tail-exp))
                 piped-app
                 (process-tail piped-app (caddr tail-exp))))]))
        ;; [(eq? (car tail-exp) '&&.)
        ;;  `(&&. ,app-exp ,(cadr tail-exp))]
        ;; [(eq? (car tail-exp) '||.)
        ;;  `(||. ,app-exp ,(cadr tail-exp))]))
  (define fun-app `(app ,fun (list ,@args) #t))
  (cond [(and (null? args) (null? tail))
         (match fun
                [(pregexp #px"^([[:word:]]+)=(.+)$" (list _ var val))
                 `(assignment ,var ,val)]
                [(list 'strexps
                       (list (pregexp #px"^([[:word:]]+)=$"
                                      (list _ var))
                             val))
                 `(assignment ,var
                              ,(match val
                                      [(list 'paren x) `(parencmd ,x)]
                                      [(list 'bracket x) `(bracketcmd ,x)]
                                      [_ val]))]
                [(list 'word-split
                       (list 'atomexps
                             (list (pregexp #px"^([[:word:]]+)=$"
                                            (list _ var))
                                   val)))
                 `(assignment ,var
                              ,(match val
                                      [(list 'paren x)
                                       `(parencmd (word-split ,x))]
                                      [(list 'bracket x)
                                       `(bracketcmd (word-split ,x))]
                                      [_ val]))]
                [_ fun-app])]
        [(null? tail)
         (match fun
                [(pregexp #px"^([[:word:]]+)=$" (list _ var))
                 `(assignment ,var ,(car args))]
                [(list 'strexps
                       (list (pregexp #px"^([[:word:]]+)=$"
                                      (list _ var))))
                 `(assignment ,var
                              ,(match (car args)
                                      [(list 'paren x) `(parencmd ,x)]
                                      [(list 'bracket x) `(bracketcmd ,x)]
                                      [_ (car args)]))]
                [(list 'word-split
                       (list 'atomexps
                             (list (pregexp #px"^([[:word:]]+)=$"
                                            (list _ var)))))
                 `(assignment ,var
                              ,(match (car args)
                                      [(list 'paren x)
                                       `(parencmd (word-split ,x))]
                                      [(list 'bracket x)
                                       `(bracketcmd (word-split ,x))]
                                      [_ (car args)]))]
                [_ fun-app])]
        [else (process-tail fun-app tail)]))

(define (bindings->argpat bindings)
  (if (null? bindings)
      ''()
      (let ([pat (bindings->argpat (cdr bindings))])
        `(or (cons ,(caar bindings) ,pat)
             (? .force (mcons ,(caar bindings) ,pat))))))

(define (binding-values blist)
  `(list ,@(map cadr blist)))

(define-logger regex)

(define (path-seg->string seg)
  (match seg
         ['same "."]
         ['up ".."]
         [s (path->string s)]))

(define (translate-globs pat)
  `(pregexp
    ,(let loop ([segs (map (compose1 translate-seg path-seg->string)
                           (explode-path pat))]
                [res '()])
       (cond [(null? (cdr segs))
              (apply string-append (reverse (list* "$" (caar segs) res)))]
             [(cadar segs)
              (loop (cdr segs) (list* "/" (caar segs) res))]
             [else
              (loop (cdr segs) (cons (caar segs) res))]))))

(define (translate-seg seg)
  (match seg
         ["**" '(".*" #f)]
         ["*" '("[^/]*" #t)]
         ["?" '("[^/]" #t)]
         [s (list
             (regexp-replaces s '(["[*]" "[^/]*"] ["[?]" "[^/]"]
                                  ["[.]" "\\\\."]))
             #t)]))

(define (extract-regexp-field-names pat)
  (log-regex-debug "PAT: ~s" pat)
  (let* ([port (if (regexp? pat)
                   (let ([s (~a pat)])
                     (open-input-string
                      (substring s 4 (sub1 (string-length s)))))
                   (open-input-string (~a pat)))]
         [match-results (rparse (lambda () (rlex port)))]
         [vars (foldr (lambda (item acc)
                        (if (eq? (car item) 'var)
                            (cons (cadr item) acc)
                            acc))
                      '()
                      match-results)]
         [regex (apply string-append
                       `("^"
                         ,@(map (lambda (item)
                                  (if (eq? (car item) 'var)
                                      (string-append
                                       "(" (quote-pars (caddr item)) ")")
                                      (quote-pars (cadr item))))
                                match-results)
                         "$"))])
    (values vars regex)))

(define (quote-pars str)
  (regexp-replace* #px"[()]" str "\\\\&"))

(define (cflatten exp)
  (match exp
    [(cons ':: rest) rest]

    [_ (list exp)]))

(define (gosh input read-state)
  (parse (mllex input read-state)))

(define (hist-tokens str)
  (let ([f (mllex str 'default)])
    (let loop ([res '()])
      (let* ([tok (f)]
             [tok-val (position-token-token tok)])
        (cond [(eq? tok-val 'EOF) (reverse (cons tok res))]
              [(or (eq? tok-val 'ATOMBOUND) (eq? tok-val 'STRBOUND))
               (loop res)]
              [else (loop (cons tok res))])))))

;;(trace gosh)

;; (define (gosh input)
;;   (define port (if (string? input) (open-input-string input) input))
;;   (parse (lambda () (lex port))))

(define-empty-tokens lex-tokens
  (REEOF RELPAR RERPAR RELDOLLAR RELWHAT NAMEOPEN NAMECLOSE))
(define-tokens lex-value-tokens (RELCHAR))

(define rlex
  (lexer [(eof) 'REEOF]
         ["\\(" (token-RELCHAR #\()]
         ["\\)" (token-RELCHAR #\))]
         ["\\$" (token-RELCHAR #\))]
         ["\\?" (token-RELCHAR #\?)]
         ["\\^" (token-RELCHAR #\^)]
         ["\\<" (token-RELCHAR #\<)]
         ["\\>" (token-RELCHAR #\>)]
         ["(" 'RELPAR]
         [")" 'RERPAR]
         ["$" 'RELDOLLAR]
         ["?" 'RELWHAT]
         ["<" 'NAMEOPEN]
         [">" 'NAMECLOSE]
 ;        [(:~ "(" ")" "$" "?" "<" ">" " " "\t" "\n" "\r")
        [(:~ "(" ")" "$" "?" "<" ">")
          (token-RELCHAR (string-ref lexeme 0))]))

(define rparse
  (parser
   (start start)
   (end REEOF)
   (tokens lex-value-tokens lex-tokens)
   (error (lambda (a b c) (error (list a b c))))
   (precs (nonassoc RELPAR RERPAR RELDOLLAR RELWHAT NAMEOPEN NAMECLOSE))
;;   (debug "/tmp/reparser")
   (grammar
    (start [() #f]
           ;; If there is an error, ignore everything before the error
           ;; and try to start over right after the error
           [(error start) $2]
           [(regex) $1])
    (regex
     [(var) `((var ,@$1))]
     [(chunk) `((chunk ,(list->string $1)))]
     [(chunk var) (list `(chunk ,(list->string $1)) `(var ,@$2))]
     [(var regex) (cons `(var ,@$1) $2)]
     [(RELPAR notwhat subre RERPAR)
      `((chunk ,(list->string `(#\( ,$2 ,@$3 #\)))))]
     [(chunk var regex) (list* `(chunk ,(list->string $1)) `(var ,@$2) $3)])
    (notwhat [(RELDOLLAR) #\$]
             [(RELCHAR) $1])
    (var
     [(RELPAR RELWHAT NAMEOPEN chunk NAMECLOSE subre RERPAR)
      `(,(list->symbol (if (eqv? (car $4) #\$) $4 (cons #\$ $4)))
        ,(list->string $6))])
    (maybereldollar
     [(RELDOLLAR) #\$]
     [() #\$])
    (subre [(subrechar) (list $1)]
           [(subrechar subre) (cons $1 $2)])
    (subrechar [(RELDOLLAR) #\$]
               [(RELWHAT) #\?]
               [(RELCHAR) $1])
    (chunk
     [(notwhat) (list $1)]
     [(notwhat chunk) (cons $1 $2)]))))

(define (list->symbol l)
  (string->symbol (list->string l)))


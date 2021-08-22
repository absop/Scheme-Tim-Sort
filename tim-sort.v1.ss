(eval-when (compile load eval) (optimize-level 3))
(meta define do-assert? #f)

(define-syntax do-assert
  (lambda (x)
    (syntax-case x ()
      [(_ expr)
       do-assert?
       #'(let ([result expr])
           (when (not result)
                 (printf "~a\n" 'expr)
                 (assert result)))]
      [else #'(void)])))

(define-syntax inc!
  (syntax-rules ()
    [(_ x) (set! x (+ x 1))]
    [(_ x d) (set! x (+ x d))]))

(define-syntax dec!
  (syntax-rules ()
    [(_ x) (set! x (- x 1))]
    [(_ x d) (set! x (- x d))]))

(define (tim-sort-range! lt? v lo hi)
  (define MIN_MERGE 32)
  (define MIN_GALLOP 7)
  (define INITIAL_TMP_STORAGE_LENGTH 256)

  (define range-length (- hi lo))
  (define min-gallop MIN_GALLOP)
  (define tmp-array)
  (define run-bases)
  (define run-lengths)
  (define stack-size 0)
  (define stack-length
    (cond
      [(< range-length 120) 5]
      [(< range-length 1542) 10]
      [(< range-length 119151) 24]
      [else 40]))
  (define (init-stack-and-tmp-array)
    (set! run-bases (make-fxvector stack-length))
    (set! run-lengths (make-fxvector stack-length))
    (set! tmp-array
          (make-vector
           (if (< range-length (* 2 INITIAL_TMP_STORAGE_LENGTH))
               (fxsll range-length 1)
               INITIAL_TMP_STORAGE_LENGTH))))
  (define-syntax t-get
    (syntax-rules ()
      [(_ i) (vector-ref tmp-array i)]))

  (define-syntax v-get
    (syntax-rules () [(_ i) (vector-ref v i)]))
  (define-syntax v-set!
    (syntax-rules ()
      [(_ i val) (vector-set! v i val)]))

  (define-syntax rb-get
    (syntax-rules ()
      [(_ i) (fxvector-ref run-bases i)]))
  (define-syntax rb-set!
    (syntax-rules ()
      [(_ i val) (fxvector-set! run-bases i val)]))

  (define-syntax rl-get
    (syntax-rules ()
      [(_ i) (fxvector-ref run-lengths i)]))
  (define-syntax rl-set!
    (syntax-rules ()
      [(_ i val) (fxvector-set! run-lengths i val)]))

  (define (push-run! run-base run-length)
    (rb-set! stack-size run-base)
    (rl-set! stack-size run-length)
    (inc! stack-size))

  (define (tmp-array-length min-gallop)
    (let ([new-size min-gallop])
      (set! new-size (logor new-size (fxsrl new-size 1)))
      (set! new-size (logor new-size (fxsrl new-size 2)))
      (set! new-size (logor new-size (fxsrl new-size 4)))
      (set! new-size (logor new-size (fxsrl new-size 8)))
      (set! new-size (logor new-size (fxsrl new-size 16)))
      (set! new-size (+ new-size 1))
      (if (< new-size 0)
          min-gallop
          (min new-size (fxsra range-length 1)))))

  (define (ensure-capacity! min-gallop)
    (if (< (vector-length tmp-array) min-gallop)
        (let ([len (tmp-array-length min-gallop)])
          ; (printf "[94] old-length: ~a\n" (vector-length tmp-array))
          ; (printf "[95] new-length: ~a\n" len)
          (set! tmp-array (make-vector len)))))

  (define (vector-copy! vsrc isrc vdst idst len)
    (define-syntax copy-loop
      (syntax-rules ()
        [(_ end* isrc* idst* next predict)
         (let ([end end*])
           (let loop ([isrc isrc*] [idst idst*])
             (when (predict isrc end)
                   (vector-set! vdst
                                idst
                                (vector-ref vsrc isrc))
                   (loop (next isrc 1) (next idst 1)))))]))
    (if (eq? vsrc vdst)
        (cond
          [(< isrc idst)
           (copy-loop isrc (+ isrc len -1) (+ idst len -1) - >=)]
          [(> isrc idst) (copy-loop (+ isrc len) isrc idst + <)]
          [else #f])
        (copy-loop (+ isrc len) isrc idst + <)))

  (define (binary-insertion-sort lo hi start)
    (do-assert (and (<= lo start) (<= start hi)))

    (let for ([start (or (and (= start lo) (+ start 1)) start)])
      (when (< start hi)
            (let ([pivot (v-get start)])
              (do-assert (<= lo start))
              (let while ([left lo] [right start])
                (if (< left right)
                    (let ([mid (fxsrl (+ left right) 1)])
                      (if (lt? pivot (v-get mid))
                          (while left mid)
                          (while (+ mid 1) right)))
                    (let ([n (- start left)])
                      (do-assert (= left right))
                      (cond
                        [(= n 2)
                         (v-set! (+ left 2) (v-get (+ left 1)))
                         (v-set! (+ left 1) (v-get left))]
                        [(= n 1) (v-set! (+ left 1) (v-get left))]
                        [else (vector-copy! v left v (+ left 1) n)])
                      (v-set! left pivot)))))
            (for (+ start 1)))))

  (define (reverse-range lo hi)
    (if (< lo hi)
        (let ([t (v-get lo)])
          (v-set! lo (v-get hi))
          (v-set! hi t)
          (reverse-range (+ lo 1) (- hi 1)))))

  (define (count-run-and-make-ascending lo hi)
    (do-assert (< lo hi))

    (let ([run-hi (+ lo 1)])
      (cond
        [(= run-hi hi) 1]
        [(lt? (v-get run-hi) (v-get lo))
         (let while ([run-hi (+ run-hi 1)])
           (if (and (< run-hi hi)
                    (lt? (v-get run-hi) (v-get (- run-hi 1))))
               (while (+ run-hi 1))
               (begin
                 (reverse-range lo (- run-hi 1))
                 (- run-hi lo))))]
        [else
         (let while ([run-hi (+ run-hi 1)])
           (if (and (< run-hi hi)
                    (not (lt? (v-get run-hi) (v-get (- run-hi 1)))))
               (while (+ run-hi 1))
               (- run-hi lo)))])))

  (define (compute-min-run-length n)
    (do-assert (>= n 0))
    (let while ([r 0] [n n])
      (if (>= n MIN_MERGE)
          (while (logor r (logand n 1)) (fxsrl n 1))
          (+ n r))))

  (define (merge-collapse)
    (define (helper n)
      (cond
        [(and (> n 0)
              (<= (rl-get (- n 1)) (+ (rl-get n) (rl-get (+ n 1)))))
         (if (< (rl-get (- n 1)) (rl-get (+ n 1)))
             (- n 1)
             n)]
        [(<= (rl-get n) (rl-get (+ n 1))) n]
        [else #f]))
    (if (> stack-size 1)
        (let ([n (helper (- stack-size 2))])
          (when (not (eq? n #f))
                (merge-at n)
                (merge-collapse)))))

  (define (merge-force-collapse)
    (define (helper n)
      (if (and (> n 0) (< (rl-get (- n 1)) (rl-get (+ n 1))))
          (- n 1)
          n))
    (when (> stack-size 1)
          (merge-at (helper (- stack-size 2)))
          (merge-force-collapse)))

  (define-syntax compute-with-hint1
    (syntax-rules ()
      [(_ hint)
       (lambda (last-ofs ofs)
         (values (+ last-ofs hint) (+ ofs hint)))]))
  (define-syntax compute-with-hint2
    (syntax-rules ()
      [(_ hint)
       (lambda (last-ofs ofs)
         (values (- hint ofs) (- hint last-ofs)))]))
  (define-syntax gallop
    (syntax-rules ()
      [(_ max-ofs* lt?-with-ofs compute-with-hint last-while-loop)
       (let ([max-ofs max-ofs*])
         (let while ([last-ofs 0] [ofs 1])
           (cond
             [(and (< ofs max-ofs) (lt?-with-ofs ofs))
              (while ofs
                     (let ([ofs (+ (fxsll ofs 1) 1)])
                       (if (<= ofs 0)
                           max-ofs
                           ofs)))]
             [else
              (let ([ofs (if (> ofs max-ofs) max-ofs ofs)])
                (call-with-values
                 (lambda ()
                   (compute-with-hint last-ofs ofs))
                 last-while-loop))])))]))

  (define (gallop-left key a base len hint)
    (define-syntax get
      (syntax-rules () [(_ i) (vector-ref a i)]))

    (define (last-while last-ofs ofs)
      (do-assert (and (<= -1 last-ofs) (< last-ofs ofs) (<= ofs len)))
      (let while ([last-ofs (+ last-ofs 1)] [ofs ofs])
        (cond
          [(< last-ofs ofs)
           (let ([m (+ last-ofs (fxsrl (- ofs last-ofs) 1))])
             (if (lt? (get (+ base m)) key)
                 (while (+ m 1) ofs)
                 (while last-ofs m)))]
          [else (do-assert (= last-ofs ofs)) ofs])))
    (do-assert (and (> len 0) (>= hint 0) (< hint len)))

    (if (lt? (get (+ base hint)) key)
        (gallop (- len hint)
                (lambda (ofs)
                  (lt? (get (+ base hint ofs)) key))
                (compute-with-hint1 hint)
                last-while)
        (gallop (+ hint 1)
                (lambda (ofs)
                  (not (lt? (get (- (+ base hint) ofs)) key)))
                (compute-with-hint2 hint)
                last-while)))

  (define (gallop-right key a base len hint)
    (define-syntax get
      (syntax-rules () [(_ i) (vector-ref a i)]))
    (define (last-while last-ofs ofs)
      (do-assert (and (<= -1 last-ofs) (< last-ofs ofs) (<= ofs len)))
      (let while ([last-ofs (+ last-ofs 1)] [ofs ofs])
        (cond
          [(< last-ofs ofs)
           (let ([m (+ last-ofs (fxsrl (- ofs last-ofs) 1))])
             (if (lt? key (get (+ base m)))
                 (while last-ofs m)
                 (while (+ m 1) ofs)))]
          [else (do-assert (= last-ofs ofs)) ofs])))
    (do-assert (and (> len 0) (>= hint 0) (< hint len)))

    (if (lt? key (get (+ base hint)))
        (gallop (+ hint 1)
                (lambda (ofs)
                  (lt? key (get (- (+ base hint) ofs))))
                (compute-with-hint2 hint)
                last-while)
        (gallop (- len hint)
                (lambda (ofs)
                  (not (lt? key (get (+ base hint ofs)))))
                (compute-with-hint1 hint)
                last-while)))

  (define (merge-at i)
    (do-assert (>= stack-size 2))
    (do-assert (>= i 0))
    (do-assert (or (= i (- stack-size 2)) (= i (- stack-size 3))))

    (let ([base1 (rb-get i)]
          [len1 (rl-get i)]
          [base2 (rb-get (+ i 1))]
          [len2 (rl-get (+ i 1))])
      (do-assert (and (> len1 1) (> len2 0)))
      (do-assert (= (+ base1 len1) base2))

      (rl-set! i (+ len1 len2))
      (when (= i (- stack-size 3))
            (rb-set! (+ i 1) (rb-get (+ i 2)))
            (rl-set! (+ i 1) (rl-get (+ i 2))))
      (dec! stack-size)

      (let ([k (gallop-right (v-get base2) v base1 len1 0)])
        (do-assert (>= k 0))

        (let ([base1 (+ base1 k)] [len1 (- len1 k)])
          (if (not (= len1 0))
              (let ([len2 (gallop-left (v-get (+ base1 len1 -1))
                                       v
                                       base2
                                       len2
                                       (- len2 1))])
                (do-assert (>= len2 0))
                (cond
                  [(= len2 0) #f]
                  [(<= len1 len2) (merge-lo base1 len1 base2 len2)]
                  [else (merge-hi base1 len1 base2 len2)])))))))

  (define (merge-lo base1 len1 base2 len2)
    (define (do-while1 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp)
      (do-assert (and (> len1 1) (> len2 0)))
      (cond
        [(lt? (v-get cur2) (t-get cur1))
         (v-set! dest (v-get cur2))
         (let ([dest (+ dest 1)] [cur2 (+ cur2 1)] [len2 (- len2 1)])
           (cond
             [(= len2 0) (break cur1 cur2 dest len1 len2 mgp)]
             [else
              (let ([cnt2 (+ cnt2 1)] [cnt1 0])
                (if (< (logor cnt1 cnt2) mgp)
                    (do-while1 cnt1
                               cnt2
                               cur1
                               cur2
                               dest
                               len1
                               len2
                               mgp)
                    (do-while2 cur1 cur2 dest len1 len2 mgp)))]))]
        [else (v-set! dest (t-get cur1))
              (let ([dest (+ dest 1)] [cur1 (+ cur1 1)] [len1 (- len1 1)])
                (cond
                  [(= len1 1) (break cur1 cur2 dest len1 len2 mgp)]
                  [else
                   (let ([cnt1 (+ cnt1 1)] [cnt2 0])
                     (if (< (logor cnt1 cnt2) mgp)
                         (do-while1 cnt1
                                    cnt2
                                    cur1
                                    cur2
                                    dest
                                    len1
                                    len2
                                    mgp)
                         (do-while2 cur1
                                    cur2
                                    dest
                                    len1
                                    len2
                                    mgp)))]))]))

    (define (do-while2 cur1 cur2 dest len1 len2 mgp)
      (define (continue1 cnt1 cur1 cur2 dest len1 len2 mgp)
        (v-set! dest (v-get cur2))
        (let ([dest (+ dest 1)] [cur2 (+ cur2 1)] [len2 (- len2 1)])
          (cond
            [(= len2 0) (break cur1 cur2 dest len1 len2 mgp)]
            [else
             (let ([cnt2 (gallop-left (t-get cur1) v cur2 len2 0)])
               (cond
                 [(not (= cnt2 0))
                  (vector-copy! v cur2 v dest cnt2)
                  (let ([dest (+ dest cnt2)]
                        [cur2 (+ cur2 cnt2)]
                        [len2 (- len2 cnt2)])
                    (if (= len2 0)
                        (break cur1 cur2 dest len1 len2 mgp)
                        (continue2 cnt1
                                   cnt2
                                   cur1
                                   cur2
                                   dest
                                   len1
                                   len2
                                   mgp)))]
                 [else (continue2 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp)]))])))
      (define (continue2 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp)
        (v-set! dest (t-get cur1))
        (let ([dest (+ dest 1)] [cur1 (+ cur1 1)] [len1 (- len1 1)])
          (if (= len1 1)
              (break cur1 cur2 dest len1 len2 mgp)
              (let ([mgp (- mgp 1)])
                (cond
                  [(or (>= cnt1 MIN_GALLOP) (>= cnt2 MIN_GALLOP))
                   (do-while2 cur1 cur2 dest len1 len2 mgp)]
                  [else
                   (let ([mgp (if (< mgp 0) 2 (+ mgp 2))])
                     (do-while1 0
                                0
                                cur1
                                cur2
                                dest
                                len1
                                len2
                                mgp))])))))

      (do-assert (and (> len1 1) (> len2 0)))
      (let ([cnt1 (gallop-right (v-get cur2) tmp-array cur1 len1 0)])
        (cond
          [(not (= cnt1 0))
           (vector-copy! tmp-array cur1 v dest cnt1)
           (let ([dest (+ dest cnt1)]
                 [cur1 (+ cur1 cnt1)]
                 [len1 (- len1 cnt1)])
             (if (<= len1 1)
                 (break cur1 cur2 dest len1 len2 mgp)
                 (continue1 cnt1 cur1 cur2 dest len1 len2 mgp)))]
          [else (continue1 cnt1 cur1 cur2 dest len1 len2 mgp)])))

    (define (break cur1 cur2 dest len1 len2 mgp)
      (set! min-gallop (max 1 mgp))
      (cond
        [(= len1 1)
         (do-assert (> len2 0))
         (vector-copy! v cur2 v dest len2)
         (v-set! (+ dest len2) (t-get cur1))]
        [(= len1 0)
         (do-assert (= len2 0))
         (error 'merge-lo
                "Comparison method violates its general contract!")]
        [else (do-assert (= len2 0))
              (do-assert (> len1 1))
              (vector-copy! tmp-array cur1 v dest len1)]))

    (do-assert (and (> len1 0) (> len2 0) (= (+ base1 len1) base2)))
    (ensure-capacity! len1)
    (vector-copy! v base1 tmp-array 0 len1)

    (let ([cur1 0] [cur2 base2] [dest base1])
      (v-set! dest (v-get cur2))
      (let ([dest (+ dest 1)] [cur2 (+ cur2 1)] [len2 (- len2 1)])
        (cond
          [(= len2 0) (vector-copy! tmp-array cur1 v dest len1)]
          [(= len1 1)
           (vector-copy! v cur2 v dest len2)
           (v-set! (+ dest len2) (t-get cur1))]
          [else (do-while1 0 0 cur1 cur2 dest len1 len2 min-gallop)]))))

  (define (merge-hi base1 len1 base2 len2)
    (define (do-while1 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp)
      (do-assert (and (> len1 0) (> len2 1)))
      (cond
        [(lt? (t-get cur2) (v-get cur1))
         (v-set! dest (v-get cur1))
         (let ([dest (- dest 1)] [cur1 (- cur1 1)] [len1 (- len1 1)])
           (cond
             [(= len1 0) (break cur1 cur2 dest len1 len2 mgp)]
             [else
              (let ([cnt1 (+ cnt1 1)] [cnt2 0])
                (if (< (logor cnt1 cnt2) mgp)
                    (do-while1 cnt1
                               cnt2
                               cur1
                               cur2
                               dest
                               len1
                               len2
                               mgp)
                    (do-while2 cur1 cur2 dest len1 len2 mgp)))]))]
        [else (v-set! dest (t-get cur2))
              (let ([dest (- dest 1)] [cur2 (- cur2 1)] [len2 (- len2 1)])
                (cond
                  [(= len2 1) (break cur1 cur2 dest len1 len2 mgp)]
                  [else
                   (let ([cnt2 (+ cnt2 1)] [cnt1 0])
                     (if (< (logor cnt1 cnt2) mgp)
                         (do-while1 cnt1
                                    cnt2
                                    cur1
                                    cur2
                                    dest
                                    len1
                                    len2
                                    mgp)
                         (do-while2 cur1
                                    cur2
                                    dest
                                    len1
                                    len2
                                    mgp)))]))]))

    (define (do-while2 cur1 cur2 dest len1 len2 mgp)
      (define (continue1 cnt1 cur1 cur2 dest len1 len2 mgp)
        (v-set! dest (t-get cur2))
        (let ([dest (- dest 1)] [cur2 (- cur2 1)] [len2 (- len2 1)])
          (if (= len2 1)
              (break cur1 cur2 dest len1 len2 mgp)
              (let ([cnt2 (- len2
                             (gallop-left (v-get cur1)
                                          tmp-array
                                          0
                                          len2
                                          (- len2 1)))])
                (if (not (= cnt2 0))
                    (let ([dest (- dest cnt2)]
                          [cur2 (- cur2 cnt2)]
                          [len2 (- len2 cnt2)])
                      (vector-copy! tmp-array
                                    (+ cur2 1)
                                    v
                                    (+ dest 1)
                                    cnt2)
                      (if (<= len2 1)
                          (break cur1 cur2 dest len1 len2 mgp)
                          (continue2 cnt1
                                     cnt2
                                     cur1
                                     cur2
                                     dest
                                     len1
                                     len2
                                     mgp)))
                    (continue2 cnt1
                               cnt2
                               cur1
                               cur2
                               dest
                               len1
                               len2
                               mgp))))))
      (define (continue2 cnt1 cnt2 cur1 cur2 dest len1 len2 mgp)
        (v-set! dest (v-get cur1))
        (let ([dest (- dest 1)] [cur1 (- cur1 1)] [len1 (- len1 1)])
          (if (= len1 0)
              (break cur1 cur2 dest len1 len2 mgp)
              (let ([mgp (- mgp 1)])
                (if (or (>= cnt1 MIN_GALLOP) (>= cnt2 MIN_GALLOP))
                    (do-while2 cur1 cur2 dest len1 len2 mgp)
                    (let ([mgp (if (< mgp 0) 2 (+ mgp 2))])
                      (do-while1 0
                                 0
                                 cur1
                                 cur2
                                 dest
                                 len1
                                 len2
                                 mgp)))))))
      (do-assert (and (> len1 0) (> len2 1)))
      (let ([cnt1 (- len1
                     (gallop-right (t-get cur2)
                                   v
                                   base1
                                   len1
                                   (- len1 1)))])
        (if (not (= cnt1 0))
            (let ([dest (- dest cnt1)]
                  [cur1 (- cur1 cnt1)]
                  [len1 (- len1 cnt1)])
              (vector-copy! v (+ cur1 1) v (+ dest 1) cnt1)
              (if (= len1 0)
                  (break cur1 cur2 dest len1 len2 mgp)
                  (continue1 cnt1 cur1 cur2 dest len1 len2 mgp)))
            (continue1 cnt1 cur1 cur2 dest len1 len2 mgp))))

    (define (break cur1 cur2 dest len1 len2 mgp)
      (set! min-gallop (max 1 mgp))
      (cond
        [(= len2 1)
         (do-assert (> len1 0))
         (let ([dest (- dest len1)] [cur1 (- cur1 len1)])
           (vector-copy! v (+ cur1 1) v (+ dest 1) len1)
           (v-set! dest (t-get cur2)))]
        [(= len2 0)
         (error 'merge-hi
                "Comparison method violates its general contract!")]
        [else (do-assert (= len1 0))
              (do-assert (> len2 1))
              (vector-copy! tmp-array
                            0
                            v
                            (- dest (- len2 1))
                            len2)]))

    (do-assert (and (> len1 0) (> len2 0) (= (+ base1 len1) base2)))
    (ensure-capacity! len2)
    (vector-copy! v base2 tmp-array 0 len2)

    (let ([cur1 (+ base1 len1 -1)]
          [cur2 (- len2 1)]
          [dest (+ base2 len2 -1)])
      (v-set! dest (v-get cur1))
      (let ([dest (- dest 1)] [cur1 (- cur1 1)] [len1 (- len1 1)])
        (cond
          [(= len1 0)
           (vector-copy! tmp-array
                         0
                         v
                         (- dest (- len2 1))
                         len2)]
          [(= len2 1)
           (let ([dest (- dest len1)] [cur1 (- cur1 len1)])
             (vector-copy! v (+ cur1 1) v (+ dest 1) len1)
             (v-set! dest (t-get cur2)))]
          [else (do-while1 0 0 cur1 cur2 dest len1 len2 min-gallop)]))))

  (do-assert (>= range-length 1))

  (if (>= range-length 2)
      (if (< range-length MIN_MERGE)
          (let ([init-run-len (count-run-and-make-ascending lo hi)])
            (binary-insertion-sort lo hi (+ lo init-run-len)))
          (let ([min-run-len (compute-min-run-length range-length)])
            (init-stack-and-tmp-array)
            (let do-while ([n-remaining range-length] [lo lo])
              (let ([run-len (count-run-and-make-ascending lo hi)])
                (if (< run-len min-run-len)
                    (let ([force (min n-remaining min-run-len)])
                      (binary-insertion-sort
                       lo
                       (+ lo force)
                       (+ lo run-len))
                      (set! run-len force)))
                (push-run! lo run-len)
                (merge-collapse)
                (cond
                  [(> n-remaining run-len)
                   (do-while (- n-remaining run-len)
                             (+ lo run-len))]
                  [else (do-assert (= (+ lo run-len) hi))
                        (merge-force-collapse)
                        (do-assert (= stack-size 1))]))))))
  v)

(define (tim-sort! lt? v)
  (tim-sort-range! lt? v 0 (vector-length v)))

(define (tim-sort lt? v)
  (tim-sort! lt? (vector-copy v)))


; Test
(include "test.ss")


#|
Check stability with v: #((0 . 0) (1 . 1) (2 . 2) (0 . 3) (1 . 4) (2 . 5))
    (tim-sort    <  v): #((0 . 0) (0 . 3) (1 . 1) (1 . 4) (2 . 2) (2 . 5))
    (vector-sort <  v): #((0 . 0) (0 . 3) (1 . 1) (1 . 4) (2 . 2) (2 . 5))

    (tim-sort    >  v): #((2 . 2) (2 . 5) (1 . 1) (1 . 4) (0 . 0) (0 . 3))
    (vector-sort >  v): #((2 . 2) (2 . 5) (1 . 1) (1 . 4) (0 . 0) (0 . 3))

    (tim-sort    <= v): #((0 . 3) (0 . 0) (1 . 4) (1 . 1) (2 . 5) (2 . 2))
    (vector-sort <= v): #((0 . 3) (0 . 0) (1 . 4) (1 . 1) (2 . 5) (2 . 2))

    (tim-sort    >= v): #((2 . 5) (2 . 2) (1 . 4) (1 . 1) (0 . 3) (0 . 0))
    (vector-sort >= v): #((2 . 5) (2 . 2) (1 . 4) (1 . 1) (0 . 3) (0 . 0))


Bench with size=10000000, range=1000000
(time (tim-sort < ...))
    12 collections
    6.453125000s elapsed cpu time, including 0.265625000s collecting
    6.597615400s elapsed real time, including 0.265852200s collecting
    204098304 bytes allocated, including 157804064 bytes reclaimed
comparations: 220247255, ordered: #t
(time (tim-sort < ...))
    no collections
    0.109375000s elapsed cpu time
    0.097441000s elapsed real time
    2976 bytes allocated
comparations: 9999999, ordered: #t
(time (tim-sort >= ...))
    no collections
    0.078125000s elapsed cpu time
    0.106171300s elapsed real time
    2976 bytes allocated
comparations: 9999999, ordered: #t
(time (tim-sort <= ...))
    no collections
    0.109375000s elapsed cpu time
    0.110325600s elapsed real time
    2976 bytes allocated
comparations: 9999999, ordered: #t
(time (bench-tim-sort!))
    27 collections
    15.890625000s elapsed cpu time, including 1.390625000s collecting
    16.814156600s elapsed real time, including 1.488281400s collecting
    728264256 bytes allocated, including 383489056 bytes reclaimed

(time (vector-sort < ...))
    no collections
    3.593750000s elapsed cpu time
    3.681393100s elapsed real time
    80000064 bytes allocated
comparations: 240976582, ordered: #t
(time (vector-sort < ...))
    no collections
    0.218750000s elapsed cpu time
    0.218543000s elapsed real time
    80000064 bytes allocated
comparations: 9999999, ordered: #t
(time (vector-sort >= ...))
    no collections
    1.968750000s elapsed cpu time
    2.104200800s elapsed real time
    80000064 bytes allocated
comparations: 124434623, ordered: #t
(time (vector-sort <= ...))
    no collections
    1.875000000s elapsed cpu time
    1.915505300s elapsed real time
    80000064 bytes allocated
comparations: 124434623, ordered: #t
(time (bench-vector-sort!))
    4 collections
    18.750000000s elapsed cpu time, including 1.500000000s collecting
    19.404453200s elapsed real time, including 1.565773600s collecting
    960048192 bytes allocated, including 560070944 bytes reclaimed

[Finished in 37.9s]
 |#

(defpackage :heap-pairing-elmasri-test (:use :CL :pairing-elmasri :lisp-unit))

(in-package :heap-pairing-elmasri-test)

(define-test test-basic
  (let ((heap (make-instance 'pairing-elmasri:pairing-elmasri))
        (htable (make-hash-table :test #'eql)))
    (assert-true (empty-p heap))
    (assert-eql 0 (heap-size heap))
    (dotimes (i 100)
      (let ((ii (+ i 100)))
        (setf (gethash ii htable) 
              (insert heap ii ii))))
    (assert-false (empty-p heap))
    (assert-eql 100 (heap-size heap))
    (decrease-key heap (gethash 120 htable) 50)
    (decrease-key heap (gethash 140 htable) 25)
    (decrease-key heap (gethash 160 htable) 35)
    (assert-eql 140 (peek-min heap))
    (decrease-key heap (gethash 160 htable) 15)
    (assert-eql 160 (peek-min heap))
    (assert-eql 160 (extract-min heap))
    (assert-eql 140 (peek-min heap))
    (assert-eql 140 (extract-node heap (gethash 140 htable)))
    (assert-eql 120 (extract-min heap))
    (assert-eql 100 (peek-min heap))
    (assert-eql 97 (heap-size heap))
    (clear-heap heap)
    (assert-true (empty-p heap))
    (assert-eql 0 (heap-size heap))))

(define-test test-basic-2
  (let ((heap (make-instance 'pairing-elmasri:pairing-elmasri))
        (htable (make-hash-table :test #'eql)))
    (assert-true (empty-p heap))
    (assert-eql 0 (heap-size heap))
    (dotimes (i 100)
      (let ((ii (+ i 100)))
        (setf (gethash ii htable) 
              (insert heap ii ii))))
    (assert-false (empty-p heap))
    (assert-eql 100 (heap-size heap))
    (assert-eql 100 (peek-min heap))
    (assert-eql 100 (extract-min heap))
    (extract-node heap (gethash 199 htable))
    (extract-node heap (gethash 150 htable))
    (assert-eql 101 (peek-min heap))
    (assert-eql 97 (heap-size heap))
    (loop for i from 101 to 198
          unless (= i 150)
          do (assert-eql i (extract-min heap)))
    (assert-true (empty-p heap))
    (assert-eql 0 (heap-size heap))))

(define-test test-cascading
  (let* ((heap (make-instance 'pairing-elmasri))
         (list (loop for i in '(7 6 5 4 3 2 1)
                     collect (insert heap i i))))
    (assert-eql 7 (heap-size heap))
    (extract-min heap)
    (decrease-key heap (car list) 1) ; set key of node 7 to 1
    (decrease-key heap (car (subseq list 2)) 0) ; set key of node 5 to 0
    (decrease-key heap (car (subseq list 3)) -1) ; set key of node 4 to -1
    (dolist (value '(4 5 7 2 3 6))
      (assert-eql value (extract-min heap)))
    (assert-eql 0 (heap-size heap))))

(define-test test-multiple-keys
  (let ((heap (make-instance 'pairing-elmasri:pairing-elmasri)))
    (loop for i in '(2 3 2 4 1 2)
          do (insert heap i i))
    (assert-eql 6 (heap-size heap))
    (assert-eql 1 (extract-min heap))
    (assert-eql 2 (extract-min heap))
    (assert-eql 2 (extract-min heap))
    (assert-eql 2 (extract-min heap))
    (assert-eql 3 (extract-min heap))
    (assert-eql 4 (extract-min heap))
    (assert-eql 0 (heap-size heap))))

(define-test test-mk
  (let ((heap (make-instance 'pairing-elmasri:pairing-elmasri)))
    (loop for i in '(2 4 2 3 1)
          do (insert heap i i))
    (assert-eql 1 (extract-min heap))
    (assert-eql 2 (extract-min heap))
    (assert-eql 2 (extract-min heap))
    (assert-eql 3 (extract-min heap))
    (assert-eql 4 (extract-min heap))))

(define-test test-stress
  (let ((heap (make-instance 'pairing-elmasri:pairing-elmasri))
        (size 75000))
    (assert-true (empty-p heap))
    (assert-eql 0 (heap-size heap))
    (let ((list (remove-duplicates (loop for i below size
                                         collect (random most-positive-fixnum)))))
      (dolist (key list)
        (insert heap key key))
      (assert-false (empty-p heap))
      (dolist (key (sort list #'<))
        (assert-true (= key (extract-min heap)))))
    (assert-true (empty-p heap))
    (assert-eql 0 (heap-size heap))))

(define-test test-multiple-keys-stress
  (let ((heap (make-instance 'pairing-elmasri:pairing-elmasri))
        (size 350)
        (key-range 100))
    (assert-true (empty-p heap))
    (assert-eql 0 (heap-size heap))
    (let ((list (loop for i below size
                      collect (random key-range))))
      (dolist (key list)
        (insert heap key key))
      (assert-false (empty-p heap))
      (dolist (key (sort list #'<))
        (assert-true (= key (extract-min heap)))))
    (assert-true (empty-p heap))
    (assert-eql 0 (heap-size heap))))

(define-test test-meld
  (let ((heap-1 (make-instance 'pairing-elmasri:pairing-elmasri))
        (heap-2 (make-instance 'pairing-elmasri:pairing-elmasri)))
    (assert-true (empty-p heap-1))
    (assert-eql 0 (heap-size heap-1))
    (assert-true (empty-p heap-2))
    (assert-eql 0 (heap-size heap-2))
    (loop for i in '(1 2 3 4 5)
          do (insert heap-1 i i))
    (assert-false (empty-p heap-1))
    (assert-eql 5 (heap-size heap-1))
    (loop for i in '(6 7 8 9 10)
          do (insert heap-2 i i))
    (assert-false (empty-p heap-2))
    (assert-eql 5 (heap-size heap-2))
    (let ((melded-heap (meld heap-1 heap-2)))
      (assert-false (empty-p melded-heap))
      (assert-eql 10 (heap-size melded-heap))
      (loop for i in '(1 2 3 4 5 6 7 8 9 10)
            do (assert-eql i (extract-min melded-heap)))
      (assert-true (empty-p melded-heap))
      (assert-eql 0 (heap-size melded-heap)))))

(define-test test-meld-2
  (let ((heap-1 (make-instance 'pairing-elmasri:pairing-elmasri))
        (heap-2 (make-instance 'pairing-elmasri:pairing-elmasri)))
    (assert-true (empty-p heap-1))
    (assert-eql 0 (heap-size heap-1))
    (assert-true (empty-p heap-2))
    (assert-eql 0 (heap-size heap-2))
    (loop for i in '(0 1 2 3 4 5)
          do (insert heap-2 i i))
    (assert-false (empty-p heap-2))
    (assert-eql 6 (heap-size heap-2))
    (loop for i in '(6 7 8 9 10)
          do (insert heap-1 i i))
    (assert-false (empty-p heap-1))
    (assert-eql 5 (heap-size heap-1))
    (let ((melded-heap (meld heap-1 heap-2)))
      (assert-false (empty-p melded-heap))
      (assert-eql 11 (heap-size melded-heap))
      (loop for i in '(0 1 2 3 4 5 6 7 8 9 10)
            do (assert-eql i (extract-min melded-heap)))
      (assert-true (empty-p melded-heap))
      (assert-eql 0 (heap-size melded-heap)))))

(defun timing ()
  (let ((heap (make-instance 'pairing-elmasri:pairing-elmasri))
        (size 100000)
        list)
    (dotimes (i size)
      (let ((key (random most-positive-fixnum)))
        (push key list)))
    (time
     (progn
       (loop for i in list
             do (insert heap i i))
       (dotimes (i size)
         (extract-min heap))))))

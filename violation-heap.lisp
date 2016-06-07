;;;; MINHEAP is by Stephan Frank <defclass@googlemail.com>, 2007-2012.
;;;;
;;;; Permission is hereby granted, free of charge, to any person obtaining
;;;; a copy of this software and associated documentation files (the
;;;; "Software"), to deal in the Software without restriction, including
;;;; without limitation the rights to use, copy, modify, merge, publish,
;;;; distribute, sublicense, and/or sell copies of the Software, and to
;;;; permit persons to whom the Software is furnished to do so, subject to
;;;; the following conditions:
;;;;
;;;; The above copyright notice and this permission notice shall be included
;;;; in all copies or substantial portions of the Software.
;;;;
;;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;;;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;;;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;;;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;;;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

(defpackage :violation-heap (:use :cl)
  (:export
   #:violation-heap
   #:clear-heap
   #:empty-p
   #:insert
   #:peek-min
   #:extract-min
   #:extract-node
   #:heap-size
   #:decrease-key
   #:meld
   ))

(in-package :violation-heap)

;;;; Implementation of Violation Heaps based on "Amr Elmasry:
;;;; 'Violation Heaps: A Better Substitude for Fibnoacci Heaps',
;;;; arXiv:0812.2851v1

;;; performance seems fine now, finally, but see FIXME below about the
;;; one unclear discrepancy between this implementation/my
;;; understanding and the paper.

(defstruct (node (:constructor %make-node (key data)))
  (key 0 :type fixnum)
  (data nil)
  (prev nil :type (or null node))
  (next nil :type (or null node))
  (child nil :type (or null node))
  (rank 0 :type (integer 0 #.most-positive-fixnum))
  (goodness 0 :type (integer 0 #.most-positive-fixnum)))

(defclass violation-heap ()
  ((size :initform 0 :initarg :size
         :type (integer 0 *))
   (rootlist :initform nil :initarg :rootlist
             :type (or null node))))

(defmethod print-object ((obj violation-heap) stream)
  (print-unreadable-object (obj stream :type t :identity t)
    (format stream "~4I~:_size: ~A~:_" (slot-value obj 'size))))

(defun heap-size (heap)
  (slot-value heap 'size))

(defun empty-p (heap)
  (zerop (slot-value heap 'size)))

(defun clear-heap (heap)
  (setf (slot-value heap 'size) 0
        (slot-value heap 'rootlist) nil)
  heap)

(defun insert (heap key data)
  (let ((node (%make-node key data))
        (rootlist (slot-value heap 'rootlist)))
    ;; make node member of a circular singleton list
    (make-singular-list node) 
    (incf (slot-value heap 'size))
    ;; attach node to root-list
    (cond
      ((null rootlist)
       (setf (slot-value heap 'rootlist) node))
      (t
       (setf (slot-value heap 'rootlist)
             (join-lists rootlist node))
       node))))

(defun peek-min (heap)
  (let ((node (slot-value heap 'rootlist)))
    (assert node)
    (values (node-data node)
            (node-key  node))))

(defun extract-min (heap)
  (let ((min-node (slot-value heap 'rootlist)))
    (assert min-node)
    ;; extract MIN-NODE from circular root list
    (decf (slot-value heap 'size))
    (if (eq min-node (node-prev min-node))
        (setf (slot-value heap 'rootlist) nil) ; singleton list case
        (setf (node-prev (node-next min-node))
              (node-prev min-node)
              (node-next (node-prev min-node))
              (node-next min-node)
              (slot-value heap 'rootlist)
              (node-next min-node)
              (node-next min-node) nil
              (node-prev min-node) nil))
    ;; make each child node a member of the root list
    (loop for c = (node-child min-node)
          while c
          do (setf (slot-value heap 'rootlist)
                   (if (slot-value heap 'rootlist)
                       (join-lists (slot-value heap 'rootlist)
                                   (cut-child min-node c))
                       (cut-child min-node c))))
    ;; cleaning phase
    (when (slot-value heap 'rootlist)
      (cleaning heap))
    ;; finally return min node values
    (values (node-data min-node)
            (node-key min-node))))

(defun decrease-key (heap node key)
  (if (< (node-key node) key)
      (error "Cannot decrease key: new key greater than current key.")
      (setf (node-key node) key))
  (setf (node-key node) key)
  (let ((root (slot-value heap 'rootlist)))
    (cond
      ((root-p root node)
       (when (and (< key (node-key root))
                  (not (eq node root)))
         (setf (slot-value heap 'rootlist)
               (to-front root node))))
      (t
       (let ((parent (1st/2nd-child-p node)))
         (when parent
           (setf (slot-value heap 'rootlist)
                 (join-lists (slot-value heap 'rootlist)
                             (cut-child parent node)))
           (when (< key (node-key parent))
             (loop for p = parent then (1st/2nd-child-p p)
                   while (and p
                              (let ((goodness (goodness p)))
                                (prog1 (< goodness (node-goodness p))
                                  (setf (node-goodness p)
                                        goodness))))))))))
    node))

(defun extract-node (heap node)
  (let ((key (node-key node))
        (value (node-data node)))
    (decrease-key heap node most-negative-fixnum)
    (extract-min heap)
    (values value key)))

(defun meld (heap-a heap-b)
  (let ((rootlist-a (slot-value heap-a 'rootlist))
        (rootlist-b (slot-value heap-b 'rootlist)))
    (setf (slot-value heap-a 'rootlist)
          (cond 
            ;; cases for merge with at least one empty heap
            ((null rootlist-a)
             rootlist-b)
            ((null rootlist-b)
             rootlist-a)
            (t
             (join-lists rootlist-a rootlist-b))))
    (incf (slot-value heap-a 'size)
          (slot-value heap-b 'size))
    (clear-heap heap-b)
    heap-a))

;;; internal structure maintaining functions

(defun goodness (node)
  "Calculate new goodness value for NODE."
  (let ((first-child (node-child node)))
    (cond
      ((null first-child)
       0)
      ((null (node-next first-child))
       (1+ (floor (node-goodness first-child) 2)))
      (t 
       (let ((g1 (node-goodness first-child))
             (g2 (node-goodness (node-next first-child))))
         (+ (floor (+ g1 g2) 2) 2))))))

(defun link (node-a node-b)
  (declare (optimize (speed 3) (space 0) (debug 0))
           (type node node-a node-b))
  ;; make sure node-a has the smaller key
  (when (< (node-key node-b) (node-key node-a))
    (rotatef node-a node-b))
  ;; now unlink by making node-b the first child of node-a
  (let ((child-a (node-child node-a)))
    (when child-a
      (setf (node-prev child-a) node-b))
    (setf (node-prev node-b) node-a
          (node-next node-b) child-a
          (node-child node-a) node-b)
  ;; update rank and goodness of the surving root
    (incf (node-rank node-a))
    (setf (node-goodness node-a)
          (goodness node-a)))
  node-a)

(defun unlink (parent)
  (declare (optimize (speed 3) (space 0) (debug 0)))
  (let ((child (node-child parent)))
    ;; separate left-most child of parent returning it as new separate
    ;; tree
    (when (node-next child)
      (setf (node-prev (node-next child)) parent))
    (setf (node-prev child) nil
          (node-child parent) (node-next child)
          (node-next child) nil)
    child))

(defun cleaning (heap)
  (declare (optimize (speed 3) (space 0) (debug 0)))
  (let ((A (make-array #.(ceiling (log most-positive-fixnum (/ (1+ (sqrt 5)) 2)))
                       :initial-element nil
                       :element-type '(or null node))))
    (declare (dynamic-extent A))
    ;(format t "Count A: ~A~%" (debug-root-length (slot-value heap 'rootlist)))
    ;(format t "Count A.C: ~A~%" (debug-root-count-children (slot-value heap 'rootlist)))
    ;(break "" heap)
    (loop for n = (slot-value heap 'rootlist) then next
          ;for i from 0
          with next
          with min 
          with sentinel = (slot-value heap 'rootlist)
          with max-rank fixnum = 0
          do (loop until (clean-p n)
                   do (let ((c (unlink n)))
                        ;(format t "unlink~%")
                        (attach-next n c)))
             (setf next (node-next n))
             (let ((rank (setf (node-rank n)
                               (if (node-child n)
                                   (1+ (node-rank (node-child n)))
                                   0)
                               ;; violation is reset to 0, therefore
                               ;; goodness = rank
                               (node-goodness n) (node-rank n))))
               (declare (fixnum rank))
               (assert (< rank (length A)))
               ;; link roots of equal rank such that no two trees of
               ;; the same rank remain
               (loop for r = (make-singular-list n)
                       then (link r (shiftf (aref A r-rank) nil))
                     for r-rank = (node-rank r)
                     while (aref A r-rank)
                     finally (setf (aref A r-rank) r
                                   max-rank (max max-rank r-rank))))
          until (eq next sentinel)
          finally ;(format t "Count B: ~A~%~%" i)
                  (loop for r across A
                        for i fixnum to max-rank
                        while (<= i max-rank)
                        when r
                          do (if min
                                 (setf min (join-lists min r))
                                 (setf min r))
                        finally (setf (slot-value heap 'rootlist) min)))))

(defun attach-next (node next-node)
  (shiftf (node-next next-node)
          (node-next node)
          next-node))

(defun clean-p (node)
  (declare (optimize (speed 3) (space 0) (debug 0)))
  (or (null (node-child node))
      (let* ((child-1 (node-child node))
             (child-2 (when child-1 (node-next child-1))))
        (and (no-violation-p child-1)
             (or (null child-2)
                 (and (no-violation-p child-2)
                      ;; are ranks of both children consecutive? FIXME:
                      ;; from the paper description this should be -1
                      ;; but that gives horrible performance due to
                      ;; permanent unlinking, this seems to do OK, but
                      ;; now unlink is almost never (if ever)
                      ;; triggered?! I'm certainly misunderstanding
                      ;; something.
                      (= 1 (- (node-rank child-1)
                              (node-rank child-2)))))))))

(declaim (inline no-violation-p))
(defun no-violation-p (node)
  (= (node-goodness node)
     (node-rank node)))

(defun 1st/2nd-child-p (node)
  "Returns the parent of NODE if NODE is a first or second child, NIL
otherwise."
  (let* ((sibling (node-prev node))
         (possible-parent (when sibling (node-prev sibling))))
    (when sibling
      (cond
        ((eq (node-child sibling)       ; node is first child
             node)
         sibling)
        ((eq (node-child possible-parent) ; node is second child
             sibling)
         possible-parent)
        (t
         nil)))))

(defun cut-child (parent node)
  (declare (optimize (speed 3) (space 0) (debug 0)))
  (let ((prev (node-prev node))
        (next (node-next node)))
    (cond
      ((eq prev parent)
       (setf (node-child parent)
             next)
       (when next
         (setf (node-prev next) parent)))
      (t
       (setf (node-next prev)
             next)
       (when next
         (setf (node-prev next) prev))))
    ;; cut node and make it a member of a singleton circular root-list
    (make-singular-list node)))

(defun join-lists (list-a list-b)
  "Destructively joins two circular node lists LIST-A and LIST-B
  returning the smaller of the two entry points as result."
  ;; make sure LIST-A is bound to the node with the min. key.
  (when (< (node-key list-b)
           (node-key list-a))
    (rotatef list-a list-b))
  ;; join
  (setf (node-next (node-prev list-b)) (node-next list-a)
        (node-next list-a) list-b)
  (when (eq (node-prev list-a)
              list-a)
      (setf (node-prev list-a)
            (node-prev list-b)))
  (setf (node-prev list-b) nil)
  list-a)

(defun make-singular-list (node)
  (setf (node-prev node) node
        (node-next node) node))

;;(declaim (inline root-p))
(defun root-p (min node)
  (or (eq min node)
      (null (node-prev node))))

(defun to-front (min node)
  "Puts NODE to the front of the circular list which has MIN as front
  element. Return NODE as new front element."
  (loop for n = min then next
        for next = (node-next n)
        until (eq next node)
        finally (cond
                  ((eq n min)
                   (if (eq (node-prev min) node)
                       (return
                         (setf (node-prev node) min
                               (node-prev min) nil
                               (node-next node) min
                               (node-next min) node))
                       (progn
                         (setf (node-next (node-prev min)) node)
                         (shiftf (node-prev node) (node-prev min) nil)
                         (return (join-lists node
                                             (make-singular-list min))))))
                  (t
                   (setf (node-next n) (node-next node)
                         (node-next node) min)
                   (shiftf (node-prev node) (node-prev min) nil)
                   (return node)))))


;;; debugging helpers
#+(or)
(defun debug-root-length (min-root)
  (loop for r = min-root then (node-next r)
        count r
        until (or (null (node-next r))
                  (eq (node-next r) min-root))))
#+(or)
(defun debug-root-count-children (min-root)
  (loop for r = min-root then (node-next r)
        sum (loop for c = (node-child r) then (node-next c)
                  while c count c)
        until (or (null (node-next r))
                  (eq (node-next r) min-root))))
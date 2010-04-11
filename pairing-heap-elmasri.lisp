(defpackage :pairing-elmasri (:use :CL)
  (:export
   #:pairing-elmasri
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

(in-package :pairing-elmasri)

;;;; Paring heap with improved meld due to delayed
;;;; reconstruction. Based on "Amr Elmasri, 'Pairing Heaps with
;;;; Costless Meld', arXiv:0903.4130v2, April 2009".

(defstruct (node (:constructor %make-node (key data)))
  (key 0 :type fixnum)
  (data nil)
  (pooled nil :type boolean)
  (lchild nil  :type (or null node))
  (sibling nil :type (or null node))
  (parent nil  :type (or null node)))

(defclass pairing-elmasri ()
  ((size :initform 0 :initarg :size
         :type (integer 0 *))
   (root :initform nil :initarg :root
         :type (or null node))
   (min :initform nil :initarg :min
        :type (or null node))
   (decreased :initform nil :initarg :decreased
              :type list)
   (pooled :initform 0 :initarg :pooled
           :type fixnum)))

(defmethod print-object ((obj pairing-elmasri) stream)
  (print-unreadable-object (obj stream :type t :identity t)
    (format stream "~4I~:_size: ~A~:_" (slot-value obj 'size))))

(defun heap-size (heap)
  (slot-value heap 'size))

(defun empty-p (heap)
  (zerop (slot-value heap 'size)))

(defun clear-heap (heap)
  (setf (slot-value heap 'size) 0
        (slot-value heap 'root) nil
        (slot-value heap 'min) nil
        (slot-value heap 'decreased) nil)
  heap)

(defun peek-min (heap)
  (let ((node (slot-value heap 'min)))
    (when node
      (values (node-data node)
              (node-key node)))))

(defun extract-min (heap)
  (let ((node (slot-value heap 'min)))
    (assert node)
    (clean-up heap)
    (when (setf (slot-value heap 'root) (combine-siblings node)
                (slot-value heap 'min) (slot-value heap 'root))
      (node-parent (slot-value heap 'root)) nil)
    (decf (slot-value heap 'size))
    (values (node-data node)
            (node-key node))))

(defun insert (heap key data)
  (let ((node (%make-node key data)))
    (incf (slot-value heap 'size))
    (setf (slot-value heap 'root)
          (if (slot-value heap 'root)
              (prog1 (link (slot-value heap 'root) node)
                (update-min heap node key))
              (setf (slot-value heap 'min) node)))
    node))

(defun decrease-key (heap node key)
  (cond
    ((< (node-key node) key)
     (error "Cannot decrease key: new key greater than current key."))
    (t
     (update-decrease heap node (setf (node-key node) key)))))


(defun extract-node (heap node)
  (cond
    ((eq (slot-value heap 'min) node)
     (extract-min heap))
    (t
     (clean-up heap)
     (decf (slot-value heap 'size))
     (cut-parent node)
     (let ((tmp (make-instance 'pairing-elmasri
                               :size 1
                               :min node
                               :root node)))
         ;(declare (dynamic-extent tmp))
         (prog1 (extract-min tmp)
           (when (slot-value tmp 'root)
             (meld heap tmp)))))))
#+(or)
(defun extract-node (heap node)
  (decrease-key heap node most-negative-fixnum)
  (extract-min heap))

(defun meld (heap-a heap-b)
  "Melds HEAP-A and HEAP-B into HEAP-A and returns it. HEAP-A and
HEAP-B may be modified and may have become empty after this operation."
  (when (< (slot-value heap-a 'size) (slot-value heap-b 'size))
    ;; ensure heap-b is the smaller heap
    (rotatef heap-a heap-b))
  (clean-up heap-b)
  (incf (slot-value heap-a 'size) (slot-value heap-b 'size))
  (let ((root (setf (slot-value heap-a 'root)
                    (link (slot-value heap-a 'root)
                          (slot-value heap-b 'root)))))
    (update-min heap-a 
                root
                (node-key root)))
  (clear-heap heap-b)
  heap-a)


;;; internal structure maintaining functions
;(declaim (inline update-min update-decrease))

(defun update-decrease (heap node key)
  (when (and (node-parent node)
             (not (node-pooled node)))
    (incf (slot-value heap 'pooled))
    (setf (node-pooled node) t)
    (push node (slot-value heap 'decreased)))
  (update-min heap node key))

(defun update-min (heap node key)
  (if (< key (node-key (slot-value heap 'min)))
      (setf (slot-value heap 'min) node)
      node))

(defun clean-up (heap)
  (let ((poolsize (slot-value heap 'pooled)))
    (unless (zerop poolsize)
      (let ((pool (make-array poolsize :element-type 'node
                              :initial-element (slot-value heap 'root)))
            (stepsize (ceiling (log poolsize 2))))
        (declare (dynamic-extent pool))
        ;; step i
        (loop for x in (slot-value heap 'decreased)
              for i from 0
              for x-lchild = (node-lchild x)
              for x-parent = (node-parent x)
              do (setf (node-lchild x-parent)
                       (delete-node-from-childseq x 
                                                  (node-lchild x-parent)
                                                  (when x-lchild
                                                    (cut-parent x-lchild))))
                 (setf (node-pooled x) nil
                       (aref pool i) x))
        (setf (slot-value heap 'decreased) nil
              (slot-value heap 'pooled) 0)
        ;; step ii
        (loop for i fixnum by stepsize below poolsize
              for subsize = (min stepsize (- poolsize i))
              do (let ((v (make-array subsize :displaced-to pool 
                                      :displaced-index-offset i)))
                   ;;(declare (dynamic-extent v))
                   (sort v #'> :key #'node-key)
                   (loop for j below (1- subsize)
                         do (link (aref v j) (aref v (1+ j)))
                         finally (setf (slot-value heap 'root)
                                       (link (slot-value heap 'root) (aref v j))))))))))

(defun attach-child (parent child)
  (shiftf (node-sibling child) (node-lchild parent) child)
  (setf (node-parent child) parent))

(defun link (node-a node-b)
  (cond
    ;((null node-a) node-b)
    ;((null node-b) node-a)
    ((<= (node-key node-a) (node-key node-b))
     (attach-child node-a node-b))
    (t (attach-child node-b node-a))))

(defun combine-siblings (parent)
  (pair-children parent)
  (link-children parent))

(defun pair-children (parent)
  (when (node-lchild parent)
    (loop for c1 = (shiftf (node-lchild parent) nil) then next
          for c2 = (node-sibling c1)
          with next
          do (if c2
                 (progn
                   (setf (node-sibling c1) nil
                         next (shiftf (node-sibling c2) nil))
                   (attach-child parent (link c1 c2)))
                 (attach-child parent c1))
          while (and c2 next))))

(defun link-children (parent)
  (let ((root (node-lchild parent)))
    (when root
      (loop for child = (shiftf (node-sibling root) nil) 
              then (prog1 (shiftf (node-sibling child) nil)
                     (setf root (link root child)))
            while child
            finally (return root)))))

(defun cut-parent (node)
  (let ((parent (node-parent node)))
    (when parent
      (setf (node-lchild parent)
            (delete-node-from-childseq node
                                       (node-lchild parent))))
    node))

(defun delete-node-from-childseq (node first-child &optional replace)
  (let ((first first-child))
    (if (eq node first)
        (if replace
            (setf (node-sibling replace) (node-sibling node)
                  (node-parent replace) (node-parent node)
                  first replace)
            (setf first
                  (node-sibling first)))
        (loop for c = first then next
              for next = (node-sibling c)
              until (eq node next)
              finally (if replace
                          (setf (node-sibling c) replace
                                (node-parent replace) (node-parent node)
                                (node-sibling replace) (node-sibling next))
                          (setf (node-sibling c)
                                (node-sibling next)))))
    (setf (node-parent node) nil
          (node-sibling node) nil)
    first))
